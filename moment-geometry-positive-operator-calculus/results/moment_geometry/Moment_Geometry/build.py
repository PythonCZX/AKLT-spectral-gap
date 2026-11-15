"""Build the article and optional formalization guide with PDFLaTeX/BibTeX.

On a normal TeX Live installation: python3 build.py
The private-format fallback is only used in the authoring workspace.
"""
from pathlib import Path
import json, os, re, shutil, subprocess

ROOT = Path(__file__).resolve().parent
BUILD = ROOT / 'build'
BUILD.mkdir(exist_ok=True)
env = os.environ.copy()
command = ['pdflatex']
private_format = ROOT.parent / 'render_tmp/pdflatex.fmt'
if private_format.exists():
    env.update(TEXMF='{/usr/share/texlive/texmf-dist,/usr/share/texmf,/var/lib/texmf}',
               TEXMFVAR=str(ROOT.parent/'render_tmp/texmf-var'),
               TEXMFCONFIG=str(ROOT.parent/'render_tmp/texmf-config'))
    command += ['-fmt='+str(private_format.with_suffix(''))]
    fontmap = ROOT.parent/'lab/theory_expansion/pdftex.map'
    if fontmap.exists():
        shutil.copy2(fontmap, ROOT/'pdftex.map')
command += ['-interaction=nonstopmode','-halt-on-error','-file-line-error']

records=[]
for stem in ['main'] + (['formalization'] if (ROOT/'formalization.tex').exists() else []):
    for phase in ['latex1','bibtex','latex2','latex3']:
        cmd=['bibtex',stem] if phase=='bibtex' else command+[stem+'.tex']
        result=subprocess.run(cmd,cwd=ROOT,env=env,capture_output=True,text=True)
        (BUILD/f'{stem}_{phase}.log').write_text(result.stdout+result.stderr)
        if result.returncode:
            print((result.stdout+result.stderr)[-12000:])
            raise SystemExit(result.returncode)
    from pypdf import PdfReader
    log=(ROOT/(stem+'.log')).read_text(errors='replace')
    records.append({'name':stem,'pages':len(PdfReader(ROOT/(stem+'.pdf')).pages),
       'bytes':(ROOT/(stem+'.pdf')).stat().st_size,
       'overfull_boxes':re.findall(r'Overfull \\[hv]box[^\n]*',log),
       'undefined':re.findall(r'[^\n]*(?:undefined|multiply defined)[^\n]*',log)})
(BUILD/'build_summary.json').write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps(records,indent=2))
