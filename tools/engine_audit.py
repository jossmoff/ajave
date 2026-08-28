#!/usr/bin/env python3
"""Audit which engine solves each benchmark."""
import yaml, subprocess, glob, os
from collections import Counter
from concurrent.futures import ProcessPoolExecutor, as_completed

def check_one(args):
    yml, prop = args
    try:
        d = yaml.safe_load(open(yml))
        if not d or 'input_files' not in d: return None
        inputs = [os.path.join(os.path.dirname(yml), i) for i in d['input_files']]
        ps = [p for p in d.get('properties',[]) if prop in p.get('property_file','')]
        if not ps or ps[0].get('expected_verdict') is None: return None
        exp = 'TRUE' if ps[0]['expected_verdict'] else 'FALSE'
        r = subprocess.run(['./target/release/ajave', '--property', prop, '-vv'] + inputs,
                          capture_output=True, text=True, timeout=15)
        verdict = r.stdout.strip().split('\n')[-1] if r.stdout.strip() else 'ERR'
        if verdict != exp: return None
        stderr = r.stderr
        if verdict == 'FALSE':
            for line in stderr.split('\n'):
                if 'publishing violation' in line:
                    if 'concrete' in line: return 'concrete-F'
                    elif 'smt-bmc' in line: return 'smt-bmc-F'
                    elif 'nra' in line: return 'nra-F'
                    elif 'chc' in line: return 'chc-F'
                    else: return 'other-F'
        else:
            for line in stderr.split('\n'):
                if 'k-induction' in line and 'discharged' in line and 'discharged 0' not in line: return 'kinduction-T'
                if 'chc' in line and 'discharged' in line and 'discharged 0' not in line: return 'chc-T'
                if 'imc' in line and 'discharged' in line and 'discharged 0' not in line: return 'imc-T'
                if 'cegar' in line and 'discharged' in line and 'discharged 0' not in line: return 'cegar-T'
            if 'round 0: phase=Presolve open=0' in stderr: return 'ai-T'
            return 'bmc-T'
    except Exception:
        return None

if __name__ == '__main__':
    ymls = sorted(glob.glob('sv-benchmarks/*/*.yml'))
    work = [(y, p) for y in ymls for p in ['valid-assert', 'no-runtime-exception']]

    engine_map = Counter()
    with ProcessPoolExecutor(max_workers=6) as pool:
        futs = {pool.submit(check_one, w): w for w in work}
        done = 0
        for fut in as_completed(futs):
            r = fut.result()
            if r: engine_map[r] += 1
            done += 1
            if done % 200 == 0:
                print(f"  ... {done}/{len(work)} done")

    total = sum(engine_map.values())
    print(f'Total correct: {total}')
    print('Engine contributions:')
    for eng, count in engine_map.most_common():
        pct = 100*count/total if total else 0
        print(f'  {eng:20s}: {count:4d} ({pct:.1f}%)')
