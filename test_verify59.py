"""End-to-end regression tests for fail-closed 59_8 proof replay.

All mutations occur in temporary copies, never in the research tree.
The test runner deliberately invokes optimized Python, which strips assert.
"""
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
NEEDED = (
    'verify59.py', 'sieve.py', 'fastsieve2.py', 'finish59.py',
    'controls59.py', 'sieve59.json', 'finish59.json', 'controls59.json',
)

class ReplayTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        for filename in NEEDED:
            shutil.copy2(HERE / filename, self.root / filename)

    def run_replay(self, optimized):
        command = [sys.executable]
        if optimized:
            command.append('-O')
        command.append(str(self.root / 'verify59.py'))
        return subprocess.run(command, cwd=self.root, capture_output=True,
                              text=True, timeout=180)

    def test_normal_and_optimized_replay(self):
        for optimized in (False, True):
            proc = self.run_replay(optimized)
            self.assertEqual(proc.returncode,0,proc.stdout+proc.stderr)
            self.assertIn('PASS: parity-free',proc.stdout)

    def test_optimized_rejects_corrupted_saved_outputs(self):
        edits = (
            ('sieve59.json','partitions',1),
            ('finish59.json','hasse_C59',{'p':353,'hasse':1}),
            ('controls59.json','det_equals_64_F118_sq',False),
        )
        for filename,key,badvalue in edits:
            path=self.root/filename
            original=path.read_bytes()
            try:
                doc=json.loads(original)
                doc[key]=badvalue
                path.write_text(json.dumps(doc),encoding='utf-8')
                proc=self.run_replay(True)
                self.assertNotEqual(proc.returncode,0,(filename,proc.stdout))
                self.assertIn(filename+' differs from replay',proc.stderr)
            finally:
                path.write_bytes(original)

    def test_optimized_rejects_broken_moment_sieve(self):
        path=self.root/'fastsieve2.py'
        with path.open('a',encoding='utf-8') as stream:
            stream.write('\nfeasible = lambda *args, **kwargs: True\n')
        proc=self.run_replay(True)
        self.assertNotEqual(proc.returncode,0,proc.stdout)
        self.assertIn('parity-free moment',proc.stderr)

if __name__=='__main__':
    unittest.main()
