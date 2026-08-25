//! A hand-rolled `.class` reader.
//!
//! Only what the lifter needs: constant pool, fields, methods, the `Code`
//! attribute and its exception table. Everything else is skipped by length.
//! Errors are values, never panics — a malformed input must degrade to UNKNOWN.

pub type R<T> = Result<T, String>;

pub struct Reader<'a> {
    b: &'a [u8],
    p: usize,
}

impl<'a> Reader<'a> {
    pub fn new(b: &'a [u8]) -> Self {
        Reader { b, p: 0 }
    }
    fn need(&self, n: usize) -> R<()> {
        if self.p + n > self.b.len() {
            Err(format!("truncated classfile at offset {}", self.p))
        } else {
            Ok(())
        }
    }
    pub fn u1(&mut self) -> R<u8> {
        self.need(1)?;
        let v = self.b[self.p];
        self.p += 1;
        Ok(v)
    }
    pub fn u2(&mut self) -> R<u16> {
        self.need(2)?;
        let v = u16::from_be_bytes([self.b[self.p], self.b[self.p + 1]]);
        self.p += 2;
        Ok(v)
    }
    pub fn u4(&mut self) -> R<u32> {
        self.need(4)?;
        let v = u32::from_be_bytes([
            self.b[self.p],
            self.b[self.p + 1],
            self.b[self.p + 2],
            self.b[self.p + 3],
        ]);
        self.p += 4;
        Ok(v)
    }
    pub fn take(&mut self, n: usize) -> R<&'a [u8]> {
        self.need(n)?;
        let s = &self.b[self.p..self.p + n];
        self.p += n;
        Ok(s)
    }
    pub fn skip(&mut self, n: usize) -> R<()> {
        self.need(n)?;
        self.p += n;
        Ok(())
    }
}

/// Constant pool entries. We keep only the shapes we resolve against; the rest
/// collapse to `Other` but still occupy their slot so indices stay correct.
#[derive(Clone, Debug)]
pub enum Cp {
    Utf8(String),
    Int(i32),
    Float(f32),
    Long(i64),
    Double(f64),
    Class(u16),
    Str(u16),
    Field(u16, u16),
    Method(u16, u16),
    IfaceMethod(u16, u16),
    NameAndType(u16, u16),
    /// `invokedynamic`: bootstrap_method_attr_index, name_and_type_index.
    InvokeDynamic(u16, u16),
    Other,
    /// The dead second slot of a Long or Double. Present so that pool indices
    /// line up with the spec's 1-based, gappy numbering.
    Unusable,
}

#[derive(Clone, Debug)]
pub struct Handler {
    pub start: u16,
    pub end: u16,
    pub target: u16,
    /// Constant-pool class index, or 0 meaning "any" (a `finally` block).
    pub catch_type: u16,
}

#[derive(Clone, Debug)]
pub struct Code {
    pub max_stack: u16,
    pub max_locals: u16,
    pub bytes: Vec<u8>,
    pub handlers: Vec<Handler>,
    /// (bytecode offset, source line) from LineNumberTable. Needed for
    /// witnesses, which are expressed in terms of source positions.
    pub lines: Vec<(u16, u16)>,
}

#[derive(Clone, Debug)]
pub struct Method {
    pub name: String,
    pub desc: String,
    pub access: u16,
    pub code: Option<Code>,
}

#[derive(Clone, Debug)]
pub struct Field {
    pub name: String,
    pub desc: String,
    pub access: u16,
}

/// A bootstrap method entry from the BootstrapMethods attribute.
#[derive(Clone, Debug)]
pub struct BootstrapMethod {
    /// CP index of the MethodHandle_info.
    pub method_ref: u16,
    /// CP indices of the static arguments.
    pub args: Vec<u16>,
}

#[derive(Clone, Debug)]
pub struct ClassFile {
    pub cp: Vec<Cp>,
    pub this_class: String,
    pub super_class: Option<String>,
    pub interfaces: Vec<String>,
    pub fields: Vec<Field>,
    pub methods: Vec<Method>,
    pub bootstrap_methods: Vec<BootstrapMethod>,
}

/// A resolved member reference: owner class, member name, descriptor.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MemberRef {
    pub owner: String,
    pub name: String,
    pub desc: String,
}

impl ClassFile {
    pub fn parse(data: &[u8]) -> R<ClassFile> {
        let mut r = Reader::new(data);
        if r.u4()? != 0xCAFE_BABE {
            return Err("not a classfile (bad magic)".into());
        }
        let _minor = r.u2()?;
        let _major = r.u2()?;

        let count = r.u2()? as usize;
        let mut cp = vec![Cp::Unusable; count.max(1)];
        let mut i = 1usize;
        while i < count {
            let tag = r.u1()?;
            let entry = match tag {
                1 => {
                    let len = r.u2()? as usize;
                    let raw = r.take(len)?;
                    // Modified UTF-8. Lossy is fine here: we only compare
                    // identifiers and descriptors, which are ASCII in practice.
                    Cp::Utf8(String::from_utf8_lossy(raw).into_owned())
                }
                3 => Cp::Int(r.u4()? as i32),
                4 => Cp::Float(f32::from_bits(r.u4()?)),
                5 => {
                    let hi = r.u4()? as u64;
                    let lo = r.u4()? as u64;
                    Cp::Long(((hi << 32) | lo) as i64)
                }
                6 => {
                    let hi = r.u4()? as u64;
                    let lo = r.u4()? as u64;
                    Cp::Double(f64::from_bits((hi << 32) | lo))
                }
                7 => Cp::Class(r.u2()?),
                8 => Cp::Str(r.u2()?),
                9 => {
                    let a = r.u2()?;
                    let b = r.u2()?;
                    Cp::Field(a, b)
                }
                10 => {
                    let a = r.u2()?;
                    let b = r.u2()?;
                    Cp::Method(a, b)
                }
                11 => {
                    let a = r.u2()?;
                    let b = r.u2()?;
                    Cp::IfaceMethod(a, b)
                }
                12 => {
                    let a = r.u2()?;
                    let b = r.u2()?;
                    Cp::NameAndType(a, b)
                }
                15 => {
                    r.skip(3)?;
                    Cp::Other
                }
                16 | 19 | 20 => {
                    r.skip(2)?;
                    Cp::Other
                }
                17 => {
                    r.skip(4)?;
                    Cp::Other
                }
                18 => {
                    let bsm = r.u2()?;
                    let nat = r.u2()?;
                    Cp::InvokeDynamic(bsm, nat)
                }
                t => return Err(format!("unknown constant pool tag {t}")),
            };
            let wide = matches!(entry, Cp::Long(_) | Cp::Double(_));
            cp[i] = entry;
            i += if wide { 2 } else { 1 };
        }

        let _access = r.u2()?;
        let this_idx = r.u2()?;
        let super_idx = r.u2()?;

        let niface = r.u2()? as usize;
        let mut interfaces = Vec::with_capacity(niface);
        for _ in 0..niface {
            let idx = r.u2()?;
            if let Ok(n) = cp_class_name(&cp, idx) {
                interfaces.push(n);
            }
        }

        let mut fields = Vec::new();
        let nfields = r.u2()?;
        for _ in 0..nfields {
            let access = r.u2()?;
            let name = cp_utf8(&cp, r.u2()?)?;
            let desc = cp_utf8(&cp, r.u2()?)?;
            skip_attributes(&mut r)?;
            fields.push(Field { name, desc, access });
        }

        let mut methods = Vec::new();
        let nmethods = r.u2()?;
        for _ in 0..nmethods {
            let access = r.u2()?;
            let name = cp_utf8(&cp, r.u2()?)?;
            let desc = cp_utf8(&cp, r.u2()?)?;
            let mut code = None;
            let nattr = r.u2()?;
            for _ in 0..nattr {
                let aname = cp_utf8(&cp, r.u2()?)?;
                let alen = r.u4()? as usize;
                if aname == "Code" {
                    let body = r.take(alen)?;
                    code = Some(parse_code(body, &cp)?);
                } else {
                    r.skip(alen)?;
                }
            }
            methods.push(Method {
                name,
                desc,
                access,
                code,
            });
        }

        // Parse class-level attributes for BootstrapMethods.
        let mut bootstrap_methods = Vec::new();
        let nattr = r.u2()?;
        for _ in 0..nattr {
            let aname = cp_utf8(&cp, r.u2()?)?;
            let alen = r.u4()? as usize;
            if aname == "BootstrapMethods" {
                let nbsm = r.u2()?;
                for _ in 0..nbsm {
                    let method_ref = r.u2()?;
                    let nargs = r.u2()?;
                    let mut args = Vec::with_capacity(nargs as usize);
                    for _ in 0..nargs {
                        args.push(r.u2()?);
                    }
                    bootstrap_methods.push(BootstrapMethod { method_ref, args });
                }
            } else {
                r.skip(alen)?;
            }
        }

        let this_class = cp_class_name(&cp, this_idx)?;
        let super_class = if super_idx == 0 {
            None
        } else {
            Some(cp_class_name(&cp, super_idx)?)
        };

        Ok(ClassFile {
            cp,
            this_class,
            super_class,
            interfaces,
            fields,
            methods,
            bootstrap_methods,
        })
    }

    pub fn member_ref(&self, idx: u16) -> R<MemberRef> {
        let (class_idx, nat_idx) = match self.cp.get(idx as usize) {
            Some(Cp::Field(a, b)) | Some(Cp::Method(a, b)) | Some(Cp::IfaceMethod(a, b)) => {
                (*a, *b)
            }
            _ => return Err(format!("cp[{idx}] is not a member reference")),
        };
        let owner = cp_class_name(&self.cp, class_idx)?;
        let (name_idx, desc_idx) = match self.cp.get(nat_idx as usize) {
            Some(Cp::NameAndType(a, b)) => (*a, *b),
            _ => return Err(format!("cp[{nat_idx}] is not a NameAndType")),
        };
        Ok(MemberRef {
            owner,
            name: cp_utf8(&self.cp, name_idx)?,
            desc: cp_utf8(&self.cp, desc_idx)?,
        })
    }

    /// Resolve an `invokedynamic` CP entry.
    /// Returns `(name, desc, bootstrap_method_index, &bootstrap_args)`.
    pub fn invoke_dynamic(&self, idx: u16) -> R<(String, String, &BootstrapMethod)> {
        let (bsm_idx, nat_idx) = match self.cp.get(idx as usize) {
            Some(Cp::InvokeDynamic(a, b)) => (*a, *b),
            _ => return Err(format!("cp[{idx}] is not InvokeDynamic")),
        };
        let (name_idx, desc_idx) = match self.cp.get(nat_idx as usize) {
            Some(Cp::NameAndType(a, b)) => (*a, *b),
            _ => return Err(format!("cp[{nat_idx}] is not a NameAndType")),
        };
        let bsm = self.bootstrap_methods.get(bsm_idx as usize)
            .ok_or_else(|| format!("bootstrap method index {bsm_idx} out of bounds"))?;
        Ok((
            cp_utf8(&self.cp, name_idx)?,
            cp_utf8(&self.cp, desc_idx)?,
            bsm,
        ))
    }

    pub fn class_name(&self, idx: u16) -> R<String> {
        cp_class_name(&self.cp, idx)
    }

    pub fn constant(&self, idx: u16) -> Option<&Cp> {
        self.cp.get(idx as usize)
    }

    pub fn method(&self, name: &str, desc: &str) -> Option<&Method> {
        self.methods
            .iter()
            .find(|m| m.name == name && m.desc == desc)
    }
}

fn parse_code(body: &[u8], cp: &[Cp]) -> R<Code> {
    let mut r = Reader::new(body);
    let max_stack = r.u2()?;
    let max_locals = r.u2()?;
    let len = r.u4()? as usize;
    let bytes = r.take(len)?.to_vec();
    let nh = r.u2()?;
    let mut handlers = Vec::with_capacity(nh as usize);
    for _ in 0..nh {
        handlers.push(Handler {
            start: r.u2()?,
            end: r.u2()?,
            target: r.u2()?,
            catch_type: r.u2()?,
        });
    }
    // LineNumberTable is read; StackMapTable is still skipped, and becomes
    // interesting once we want verified stack heights for free rather than
    // recomputing them.
    let mut lines = Vec::new();
    let nattr = r.u2()?;
    for _ in 0..nattr {
        let aname = cp_utf8(cp, r.u2()?).unwrap_or_default();
        let alen = r.u4()? as usize;
        if aname == "LineNumberTable" {
            let body = r.take(alen)?;
            let mut lr = Reader::new(body);
            let n = lr.u2()?;
            for _ in 0..n {
                let start_pc = lr.u2()?;
                let line = lr.u2()?;
                lines.push((start_pc, line));
            }
        } else {
            r.skip(alen)?;
        }
    }
    lines.sort_unstable();
    Ok(Code {
        max_stack,
        max_locals,
        bytes,
        handlers,
        lines,
    })
}

fn skip_attributes(r: &mut Reader) -> R<()> {
    let n = r.u2()?;
    for _ in 0..n {
        let _name = r.u2()?;
        let len = r.u4()? as usize;
        r.skip(len)?;
    }
    Ok(())
}

fn cp_utf8(cp: &[Cp], idx: u16) -> R<String> {
    match cp.get(idx as usize) {
        Some(Cp::Utf8(s)) => Ok(s.clone()),
        _ => Err(format!("cp[{idx}] is not Utf8")),
    }
}

fn cp_class_name(cp: &[Cp], idx: u16) -> R<String> {
    match cp.get(idx as usize) {
        Some(Cp::Class(n)) => cp_utf8(cp, *n),
        _ => Err(format!("cp[{idx}] is not a Class")),
    }
}
