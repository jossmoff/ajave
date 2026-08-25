# Multi-stage build for ajave SV-COMP Java verifier
# Produces a minimal image with the ajave binary, JDK, and Z3.

# ── Build stage ──────────────────────────────────────────────────────
FROM rust:1.82-bookworm AS builder

WORKDIR /build
COPY Cargo.toml Cargo.lock ./
COPY crates/ crates/

# Build release binary with LTO for size
RUN cargo build --release --locked \
    && strip target/release/ajave

# ── Runtime stage ────────────────────────────────────────────────────
FROM debian:bookworm-slim

# JDK for javac (source compilation) and JVM replay (witness confirmation)
RUN apt-get update && apt-get install -y --no-install-recommends \
        default-jdk-headless \
        wget \
        ca-certificates \
    && rm -rf /var/lib/apt/lists/*

# Z3 solver — download static binary
ARG Z3_VERSION=4.13.4
RUN ARCH=$(dpkg --print-architecture) \
    && if [ "$ARCH" = "amd64" ]; then Z3_ARCH="x64"; else Z3_ARCH="$ARCH"; fi \
    && wget -q "https://github.com/Z3Prover/z3/releases/download/z3-${Z3_VERSION}/z3-${Z3_VERSION}-${Z3_ARCH}-glibc-2.35.zip" -O /tmp/z3.zip \
    && cd /tmp && apt-get update && apt-get install -y --no-install-recommends unzip && unzip z3.zip \
    && cp z3-*/bin/z3 /usr/local/bin/z3 \
    && chmod +x /usr/local/bin/z3 \
    && rm -rf /tmp/z3* \
    && apt-get purge -y unzip wget && apt-get autoremove -y \
    && rm -rf /var/lib/apt/lists/*

# Copy ajave binary
COPY --from=builder /build/target/release/ajave /usr/local/bin/ajave

# Copy benchexec tool-info and benchmark definition
COPY benchexec/ /opt/ajave/benchexec/

# Verify installation
RUN ajave --version && z3 --version && javac -version

WORKDIR /work
ENTRYPOINT ["ajave"]
