"""Reproduce the manuscript's mathematical illustrations.

All arrays come from the formulas recorded in figure_metadata.json.
Random points are used only for the explicitly labeled illustration of a
proved pointwise inequality. No surrogate data from the identity kit is used.
"""
from pathlib import Path
from collections import Counter
from fractions import Fraction
import json, math, sys, logging
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.colors import Normalize, ListedColormap
from matplotlib.patches import Circle, FancyArrowPatch, Polygon
import sympy as sp
from paper_identity import (apply_style, panel_label, export, time_cmap,
                            gradient_line, add_surface_inset)

ROOT=Path(__file__).resolve().parents[1]
logging.getLogger('fontTools').setLevel(logging.ERROR)
OUT=ROOT/'figures'
OUT.mkdir(exist_ok=True)
apply_style()
plt.rcParams.update({'font.size':10, 'axes.labelsize':12, 'axes.titlesize':11,
 'xtick.labelsize':9,'ytick.labelsize':9,'legend.fontsize':8,
 'pdf.compression':9,'figure.dpi':160,'savefig.dpi':180})
BLUE='#0077b5'; ORANGE='#dd7d20'; PURPLE='#7057a3'; TEAL='#239789'
COLORS=[BLUE,ORANGE,PURPLE]
META={}

def finish(fig,name,description,data=None):
    export(fig,OUT/name,formats=('pdf','png'),dpi=180)
    plt.close(fig)
    META[name]={'description':description,'data':data or {},'visual_review':'pending'}

def panels(axes):
    for i,ax in enumerate(np.ravel(axes)):
        panel_label(ax,chr(97+i),xy=(-.10,1.12),size=23,weight='bold',clip_on=False)

def hesse():
    w=np.exp(2j*np.pi/3); out=[]
    for a in range(3):
        b,c=[i for i in range(3) if i!=a]
        for j in range(3):
            z=np.zeros(3,complex); z[b]=1; z[c]=-w**j
            out.append(z/np.sqrt(2))
    return np.asarray(out)

def witness(z):
    z=np.asarray(z)
    return np.abs(np.sum(z**3,axis=-1))**2/3+6*np.prod(np.abs(z)**2,axis=-1)

def fig01():
    fig=plt.figure(figsize=(7.15,3.25))
    ax=fig.add_axes([.06,.19,.40,.68]); bx=fig.add_axes([.58,.22,.37,.59])
    v=np.array([[0,0],[1,0],[.5,np.sqrt(3)/2]])
    ax.add_patch(Polygon(v,facecolor='#f4f7f8',edgecolor='black',lw=.7))
    for i,p in enumerate(v):
        ax.scatter(*p,s=100,facecolor=ORANGE,edgecolor='white',zorder=4)
        ax.text(p[0]+[-.04,.04,0][i],p[1]+[-.09,-.09,.08][i],rf'$e_{i}$',ha='center')
    mids=np.array([(v[(i+1)%3]+v[(i+2)%3])/2 for i in range(3)])
    for i,p in enumerate(mids):
        ax.scatter(*p,s=125,c=BLUE,edgecolor='white',zorder=4)
        d=(p-v.mean(axis=0)); d=d/np.linalg.norm(d)
        ax.text(*(p+.12*d),'3 phases',ha='center',va='center',fontsize=8,color=BLUE)
    center=v.mean(axis=0)
    ax.scatter(*center,s=180,c=ORANGE,edgecolor='white',zorder=4)
    ax.text(center[0],center[1]-.13,'7 phases',ha='center',fontsize=8,color=ORANGE)
    ax.set(xlim=(-.2,1.2),ylim=(-.17,1.04),aspect='equal');ax.axis('off')
    ax.set_title(r'Moment-map projection $p_i=|z_i|^2$',pad=15,fontsize=10)
    ax.text(.5,-.16,'Hesse: blue     Singer: orange',ha='center',transform=ax.transAxes,fontsize=9)
    zeta=np.exp(2j*np.pi/7)
    singer=np.vstack([np.eye(3),np.array([[1,zeta**j,zeta**(3*j)] for j in range(7)])/np.sqrt(3)])
    weights=np.array([1/12]*3+[3/28]*7)
    qvals=[0, float(np.dot(weights,witness(singer))), 1/5]
    bars=bx.bar(range(3),qvals,color=[BLUE,ORANGE,'#888888'],width=.55)
    bx.scatter([0],[0],c=BLUE,s=40,zorder=3)
    for x,q in enumerate(qvals): bx.text(x,q+.012,f'{q:.3f}',ha='center',fontsize=9)
    bx.set(xticks=range(3),xticklabels=['Hesse','Singer','Haar'],ylim=(0,.36),ylabel=r'$\operatorname{tr}(Q M_3)$')
    bx.set_title('Three-copy separation',pad=22)
    bx.text(.5,.86,r'All three have $M_2=I_6/6$',ha='center',transform=bx.transAxes,fontsize=10)
    panels([ax,bx])
    finish(fig,'fig01_moment_fibres','Exact moment identities; probability-simplex projection loses phase information.',{'singer_weights':['1/12']*3+['3/28']*7,'witness_expectations':qvals})

def fig02():
    fig=plt.figure(figsize=(7.15,3.45))
    ax=fig.add_axes([.08,.18,.40,.65]);bx=fig.add_axes([.61,.18,.34,.65])
    t=np.linspace(0,2*np.pi,401); s=np.linspace(0,np.pi/2,201)
    T,S=np.meshgrid(t,s)
    Q=(np.cos(S)**6+np.sin(S)**6+2*np.cos(S)**3*np.sin(S)**3*np.cos(3*T))/3
    im=ax.imshow(Q,origin='lower',extent=[0,2,.0,.5],aspect='auto',cmap='viridis',vmin=0,vmax=1/3,rasterized=True)
    ax.contour(T/np.pi,S/np.pi,Q,levels=[.015,.06,.15,.25],colors='white',linewidths=.5,alpha=.8)
    ax.scatter([1/3,1,5/3],[.25]*3,c='white',edgecolors='black',s=22,zorder=3)
    ax.set(xlabel=r'$\theta/\pi$',ylabel=r'$s/\pi$',title=r'$z=(0,\cos s,e^{i\theta}\sin s)$')
    cb=fig.colorbar(im,cax=fig.add_axes([.08,.90,.40,.025]),orientation='horizontal')
    cb.ax.xaxis.set_ticks_position('top');cb.ax.tick_params(labelsize=8,pad=1)
    cb.set_ticks([0,1/6,1/3],labels=['0',r'$1/6$',r'$1/3$'])
    rng=np.random.default_rng(20261115)
    z=rng.normal(size=(2500,3))+1j*rng.normal(size=(2500,3)); z/=np.linalg.norm(z,axis=1)[:,None]
    q=witness(z); dist=np.sqrt(np.maximum(0,1-np.max(abs(z@hesse().conj().T)**2,axis=1)))
    bx.scatter(q,dist,s=2,c=q,cmap='viridis',alpha=.30,rasterized=True)
    xx=np.linspace(0,.34,300)
    bx.plot(xx,np.minimum(1,np.sqrt(27*xx/4)),color=ORANGE,lw=1.6,label=r'$\min\{1,\sqrt{27q/4}\}$')
    bx.set(xlim=(0,.34),ylim=(0,1.03),xlabel=r'$q(z)=\langle z^{\otimes3},Qz^{\otimes3}\rangle$',ylabel=r'$\min_h d_{\rm tr}(P_z,P_h)$')
    bx.legend(loc='lower right',fontsize=8)
    bx.set_title('Pointwise coercivity',pad=22)
    tx=np.linspace(.82,1.18,55); sy=np.linspace(.13,.37,55)
    TX,SY=np.meshgrid(tx,sy); TT=np.pi*TX; SS=np.pi*SY
    ZZ=(np.cos(SS)**6+np.sin(SS)**6+2*np.cos(SS)**3*np.sin(SS)**3*np.cos(3*TT))/3
    add_surface_inset(bx,bounds=(.49,.57,.48,.38),X=TX,Y=SY,Z=ZZ,level=.03,
                      mark_summit=False,zoom=1.15,elev=32,azim=-55)
    bx.text(.77,.91,r'$q=0.03$',ha='center',transform=bx.transAxes,fontsize=8,
            bbox={'facecolor':'white','edgecolor':'none','pad':1},zorder=10)
    panels([ax,bx])
    finish(fig,'fig02_cubic_witness','Left: exact cubic witness on a projective line. Right: seeded illustration of the proved distance bound, not its proof.',{'random_seed':20261115,'points':2500,'minimum_bound_slack':float(np.min(27*q/4-dist**2))})

def fig03():
    fig=plt.figure(figsize=(7.15,3.0))
    a,b,c=1,.65,.35
    T=np.zeros((3,3,3))
    for i in range(3):T[i,i,i]=a
    for i,j,k in [(0,1,2),(1,2,0),(2,0,1)]:T[i,j,k]=b
    for i,j,k in [(0,2,1),(2,1,0),(1,0,2)]:T[i,j,k]=c
    axs=[]
    for k in range(3):
        ax=fig.add_axes([.055+k*.235,.30,.18,.49]);axs.append(ax)
        ax.imshow(T[:,:,k],cmap='viridis',vmin=0,vmax=1,interpolation='nearest')
        for i in range(3):
            for j in range(3):
                if T[i,j,k]:ax.text(j,i,'a' if T[i,j,k]==a else 'b' if T[i,j,k]==b else 'c',ha='center',va='center',color='white',fontsize=12)
        ax.set(xticks=[0,1,2],yticks=[0,1,2],xlabel=r'$j$',ylabel=r'$i$' if k==0 else '',title=rf'$k={k}$')
    ax=fig.add_axes([.78,.31,.18,.47]);axs.append(ax)
    ax.bar([0,1,2],[1/3]*3,color=[BLUE,ORANGE,PURPLE],width=.6)
    ax.set(ylim=(0,.43),xticks=[0,1,2],yticks=[0,1/3],yticklabels=['0',r'$1/3$'],title='Each marginal')
    fig.text(.5,.10,r'$\det M(z)=(a^3+b^3+c^3)z_0z_1z_2-abc(z_0^3+z_1^3+z_2^3)$',ha='center',fontsize=12)
    fig.text(.38,.94,r'The Cartan slice in $(\mathbb{C}^3)^{\otimes3}$',ha='center',fontsize=13)
    finish(fig,'fig03_tensor_balance','Exact support of the three-qutrit Cartan tensor; color magnitudes are illustrative coefficients a=1,b=.65,c=.35. Scalar marginal identity is exact for arbitrary complex a,b,c.',{'coefficients':[a,b,c]})

def fig04():
    fig=plt.figure(figsize=(7.15,3.4))
    ax=fig.add_axes([.07,.18,.41,.67]); bx=fig.add_axes([.60,.19,.35,.64])
    M=24; vv=np.array([[0,0],[1,0],[.5,np.sqrt(3)/2]])
    aa=np.array([(i,j,M-i-j) for i in range(M+1) for j in range(M-i+1)])
    xy=aa@vv/M;cost=M-aa.max(axis=1)
    sc=ax.scatter(xy[:,0],xy[:,1],c=cost/M,cmap='viridis',s=12,linewidths=0)
    ax.add_patch(Polygon(vv,fill=False,edgecolor='black',lw=.6))
    for i in range(3):
        p=(vv[(i+1)%3]+vv[(i+2)%3])/2
        ax.plot([p[0],.5],[p[1],np.sqrt(3)/6],color='white',lw=1.2)
    ax.set(aspect='equal',xlim=(-.04,1.04),ylim=(-.04,.92)); ax.axis('off')
    fig.text(.27,.10,r'Minimal jet cost: $1-\max_i(\alpha_i/M)$',ha='center',fontsize=11)
    cb=fig.colorbar(sc,cax=fig.add_axes([.09,.89,.37,.025]),orientation='horizontal');cb.ax.xaxis.set_ticks_position('top');cb.set_ticks([0,1/3,2/3],labels=['0',r'$1/3$',r'$2/3$']);cb.ax.tick_params(labelsize=8,pad=1)
    dd=np.arange(1,31); H=np.array([sum(1/j for j in range(1,d+2)) for d in dd])
    gamma=dd/(dd+1-H)
    bx.plot(dd,gamma,'o-',ms=3,color=BLUE,lw=1)
    bx.axhline(1,color='black',lw=.7,ls='--');bx.text(20,1.035,'canonical coupling',fontsize=8)
    bx.scatter([2],[12/7],s=36,color=ORANGE,zorder=4)
    bx.annotate(r'$\Gamma^{\mathrm{bal}}(\mathbb{CP}^{2})=12/7$',xy=(2,12/7),xytext=(5,1.85),fontsize=10,arrowprops={'arrowstyle':'-','lw':.7})
    bx.set(xlabel=r'Complex dimension $d$',ylabel=r'$d/(d+1-H_{d+1})$',xlim=(0,31),ylim=(.98,2.08))
    panel_label(ax,'a',xy=(-.17,1.12),size=23,weight='bold',clip_on=False)
    panel_label(bx,'b',xy=(-.10,1.12),size=23,weight='bold',clip_on=False)
    finish(fig,'fig04_jet_geometry','Exact monomial jet cost on the degree-24 simplex; projective-dimension threshold formula with harmonic numbers.',{'degree':M,'monomials':len(aa),'S_M':int(cost.sum()),'dimensions':dd.tolist(),'thresholds':gamma.tolist()})

def fig05():
    fig=plt.figure(figsize=(7.15,3.15))
    ax=fig.add_axes([.04,.13,.31,.76]);ax.axis('off')
    ang=np.linspace(0,2*np.pi,8)[:-1]+np.pi/2
    xy=np.c_[np.cos(ang),np.sin(ang)]*.72
    ax.add_patch(Circle((0,0),.72,fill=False,edgecolor='#cccccc',lw=.7))
    ax.scatter(xy[:,0],xy[:,1],s=45,color=BLUE)
    for j,p in enumerate(xy):ax.text(*(p*1.22),str(j),ha='center',va='center',fontsize=8)
    basis=np.array([[-1.22,-.9],[1.22,-.9],[0,1.2]])
    ax.scatter(basis[:,0],basis[:,1],color=ORANGE,s=55)
    for j,p in enumerate(basis):ax.text(p[0],p[1]-.17,rf'$e_j$'.replace('j',str(j)),ha='center',fontsize=10)
    ax.text(0,.03,r'$[1:\zeta^j:\zeta^{3j}]$',ha='center',fontsize=11)
    ax.set(xlim=(-1.65,1.65),ylim=(-1.3,1.55),aspect='equal',title='Singer configuration')
    bx=fig.add_axes([.39,.13,.22,.76]);bx.axis('off')
    ys=[.87,.52,.17]
    for y,label,detail in zip(ys,['Blow up 10 points','Cyclic triple cover','Contract 3 curves'],[r'$C_i^2=-3,\ D=-3K_S$',r'$R_i^2=-1$',r'$K_X=0,\ e(X)=24$']):
        bx.text(.5,y,label,ha='center',fontsize=9)
        bx.text(.5,y-.10,detail,ha='center',fontsize=10,color=BLUE)
    for y in [.69,.34]:bx.annotate('',xy=(.5,y-.10),xytext=(.5,y+.03),arrowprops={'arrowstyle':'->','lw':.9})
    cx=fig.add_axes([.68,.20,.29,.62]);cx.axis('off')
    u=np.array([1,0]);v=np.array([-.5,np.sqrt(3)/2])
    for i in range(-2,3):
        for j in range(-2,3):
            p=i*u+j*v
            if np.linalg.norm(p)<=2.01:cx.scatter(*p,c='#bbbbbb',s=13)
    cx.add_patch(Polygon([[0,0],u,u+v,v],facecolor='#d9ecec',edgecolor=BLUE,lw=1.2))
    for p,lab in [(u,r'$v$'),(v,r'$\delta v$')]:cx.annotate('',xy=p,xytext=(0,0),arrowprops={'arrowstyle':'->','color':BLUE,'lw':1.4});cx.text(*(1.17*p),lab,color=BLUE,ha='center',fontsize=10)
    cx.set(xlim=(-2.3,2.3),ylim=(-1.8,2.05),aspect='equal',title=r'$T_X\simeq A_2(7)$')
    cx.text(0,-1.60,r'$\det T_X=147$',ha='center',fontsize=11)
    panels([ax,bx,cx])
    finish(fig,'fig05_singer_cover','Left is an abstract display of the ten labelled rays, not a Euclidean embedding of their projective incidence. Middle gives the exact cover construction. Right draws the shape of the Eisenstein lattice; its scale is fixed by Gram matrix [[14,-7],[-7,14]].')

def partitions(n):
    word=[0]*n
    def rec(j,m):
        if j==n:yield tuple(word);return
        for a in range(m+2):word[j]=a;yield from rec(j+1,max(m,a))
    yield from rec(1,0)

def trees(word):
    n=max(word)+1
    if n==1:return 1
    A=sp.zeros(n)
    for a,b in zip(word,word[1:]+word[:1]):
        if a!=b:A[a,a]+=1;A[a,b]-=1
    return int(A[:n-1,:n-1].det())

def fig06():
    fig=plt.figure(figsize=(7.15,3.35))
    ax=fig.add_axes([.045,.16,.28,.72]);ax.axis('off')
    ps=np.array([[0,1],[1,1],[1,0],[0,0]])
    for i in range(4):
        j=(i+1)%4
        ax.annotate('',xy=ps[j],xytext=ps[i],arrowprops={'arrowstyle':'->','lw':.8,'shrinkA':8,'shrinkB':8})
    for i,p in enumerate(ps):ax.scatter(*p,s=110,c=BLUE if i%2==0 else ORANGE,zorder=4);ax.text(*p,str(i+1),ha='center',va='center',color='white',fontsize=9,zorder=5)
    ax.plot([0,1],[1,0],ls='--',lw=1,color=BLUE);ax.plot([1,0],[1,0],ls='--',lw=1,color=ORANGE)
    ax.text(.5,-.35,r'$\pi=\{\{1,3\},\{2,4\}\}$',ha='center',fontsize=10)
    ax.text(.5,-.58,r'$\tau(G_\pi)=2$',ha='center',fontsize=12)
    ax.set(xlim=(-.25,1.25),ylim=(-.75,1.35),aspect='equal',title='A crossing partition')
    bx=fig.add_axes([.40,.20,.23,.61]);cx=fig.add_axes([.74,.20,.23,.61])
    d=np.arange(1,13);bx.plot(d,14+2.**(-d),'o-',color=PURPLE,ms=3)
    bx.axhline(14,color='black',ls='--',lw=.7);bx.set(xlabel=r'$d$',ylabel=r'$m_4(d)$',ylim=(13.96,14.56),title=r'$14+2^{-d}$')
    bx.annotate(r'$57/4$',xy=(2,14.25),xytext=(5,14.38),arrowprops={'arrowstyle':'-','lw':.7},fontsize=10)
    pp=range(4,8);hist={p:Counter(trees(w) for w in partitions(p)) for p in pp}
    for q,color in zip([1,2,4,8],[ORANGE,BLUE,TEAL,PURPLE]):
        vals=[sum(c/t**q for t,c in hist[p].items())/(math.comb(2*p,p)/(p+1))-1 for p in pp]
        cx.semilogy(list(pp),vals,'o-',ms=3,c=color,label=rf'$d={q}$')
    cx.set(xlabel=r'Moment order $p$',ylabel=r'$m_p(d)/C_p-1$',xticks=list(pp),title='Crossing correction')
    cx.legend(fontsize=8,loc='upper left')
    panels([ax,bx,cx])
    finish(fig,'fig06_gram_trees','Exact finite partition enumeration with integer directed-tree cofactors; no sampled spectral data.',{'tree_histograms':{str(p):dict(h) for p,h in hist.items()}})

def fig07():
    fig=plt.figure(figsize=(7.15,3.3))
    ax=fig.add_axes([.04,.20,.23,.61]);bx=fig.add_axes([.36,.20,.25,.61]);cx=fig.add_axes([.72,.20,.25,.61])
    ax.axis('off')
    for x in np.linspace(0,1,5):ax.plot([x,.5],[0,1],color='#555555',lw=.7);ax.scatter(x,0,s=45,c=BLUE)
    ax.scatter(.5,1,s=65,c=ORANGE)
    ax.text(.5,-.30,r'$\Omega_H(t)=\sum_{j=1}^{t}j^m$',ha='center',fontsize=10)
    ax.text(.5,-.70,r"$\Omega'_H(0)=B_m(1)$",ha='center',fontsize=10)
    ax.set(xlim=(-.2,1.2),ylim=(-.9,1.28),title='Star heap')
    m=np.arange(1,17);bv=np.array([float(sp.bernoulli(int(j),1)) for j in m]);nz=bv!=0
    bx.stem(m[nz],np.log10(abs(bv[nz])),linefmt='#999999',markerfmt=' ',basefmt=' ')
    bx.scatter(m[nz],np.log10(abs(bv[nz])),c=[BLUE if v>0 else ORANGE for v in bv[nz]],s=30,zorder=4)
    bx.scatter(m[~nz],[-2.3]*sum(~nz),c='#aaaaaa',s=14,marker='x')
    bx.set(xlabel=r'Leaves $m$',ylabel=r'$\log_{10}|B_m(1)|$',xticks=[1,4,8,12,16],ylim=(-2.6,1),title='Signed coefficients')
    bx.text(.03,.92,'blue +    orange -',transform=bx.transAxes,fontsize=8)
    mm=np.arange(20,201);rr=2*np.sin(np.pi/mm)
    cx.plot(mm,rr,color=BLUE);cx.axhline(1/16,c=ORANGE,ls='--',lw=1)
    cx.scatter([128],[2*np.sin(np.pi/128)],c=BLUE,s=25)
    cx.set(xlabel=r'Leaves $m$',ylabel='Taylor radius',title='Log-series radius',ylim=(0,.34))
    cx.text(110,.083,r'$a=1/16$',color=ORANGE,fontsize=10)
    panels([ax,bx,cx])
    finish(fig,'fig07_ordered_heaps','Exact order-polynomial/Bernoulli coefficients and the singularity radius 2 sin(pi/m) of the root-linear logarithmic response.',{'bernoulli':[str(sp.bernoulli(int(j),1)) for j in m],'radius_at_128':float(2*np.sin(np.pi/128))})

def fig08():
    fig=plt.figure(figsize=(7.15,3.45))
    axs=[fig.add_axes([x,.20,.24,.62]) for x in [.07,.395,.72]]
    x=np.linspace(-5,5,600);t=np.linspace(-3,3,600);rs=[.15,.35,.6,.85]
    cmap=time_cmap(); norm=Normalize(0,1)
    for r in rs:
        axs[0].plot(x,np.sinh(r*x)/(r*np.sinh(x)),c=cmap(norm(r)),label=rf'$r={r:g}$')
        p=np.sin(np.pi*r)/(2*r*(np.cosh(np.pi*t)+np.cos(np.pi*r)))
        axs[1].plot(t,p,c=cmap(norm(r)))
    axs[0].plot(x,x/np.sinh(x),c='black',ls='--',lw=.8,label=r'$r\to0$')
    axs[0].set(xlabel=r'$x$',ylabel=r'$\psi_r(x)/r$',title='Positive filter',ylim=(0,1.1));axs[0].legend(fontsize=7,loc='lower center',ncol=2)
    axs[1].set(xlabel=r'Modular time $t$',ylabel=r'$p_r(t)/r$',title='Modular-time density',ylim=(0,2.65))
    R=np.arange(1,61);omega=4.;tau=1.;exact=omega/np.sinh(omega)
    trunc=np.exp(-tau*np.cumsum(np.log1p(omega**2/(np.pi**2*R**2))))
    sr=tau*(1/6-np.cumsum(1/(np.pi**2*R**2)))
    accel=trunc*np.exp(-sr*omega**2)
    axs[2].loglog(R,abs(trunc-exact),c=BLUE,label='Truncated clock')
    axs[2].loglog(R,abs(accel-exact),c=ORANGE,label='Mean-corrected tail')
    axs[2].loglog(R,tau*omega**2/(np.pi**2*R),c=BLUE,ls='--',lw=.8)
    axs[2].loglog(R,tau*omega**4/(6*np.pi**4*R**3),c=ORANGE,ls='--',lw=.8)
    axs[2].set(xlabel=r'Clock factors $R$',ylabel='Observable error',title=r'Certified error, $x=4$')
    axs[2].legend(fontsize=7,loc='lower left')
    panels(axs)
    finish(fig,'fig08_modular_clocks','Exact normalized power-response filters and Fourier densities. Right compares exact scalar errors with the proved R^-1 and R^-3 local-commutator upper bounds.',{'r_values':rs,'frequency':omega,'tau':tau})

def delta(ell):return 2/(3.**ell+(-1)**ell)
def influence(a,b):return 2*a*b*(1+a*b)/((1-a)**2*(1-b)**2)

def fig09():
    fig=plt.figure(figsize=(7.15,3.35))
    ax=fig.add_axes([.035,.16,.31,.70]);ax.axis('off')
    coords=np.array([[0,0],[1.8,0],[.9,1.5],[-.9,1.5],[2.7,1.5]])
    edges=[(0,1),(0,2),(0,3),(1,2),(1,4)]
    for i,j in edges:
        p,q=coords[i],coords[j]
        ax.plot([p[0],q[0]],[p[1],q[1]],c='#888888',lw=1)
        for s in [.25,.4,.6,.75]:
            r=(1-s)*p+s*q;ax.scatter(*r,s=13,c=BLUE,zorder=3)
    ax.scatter(coords[:,0],coords[:,1],s=110,c=ORANGE,zorder=5)
    ax.text(.9,-.48,'arbitrary cores + mixing wires',ha='center',fontsize=9)
    ax.set(xlim=(-1.25,3.05),ylim=(-.7,2),aspect='equal',title='Core-wire network')
    bx=fig.add_axes([.425,.21,.23,.60]); cx=fig.add_axes([.75,.21,.23,.60])
    xx=np.linspace(.002,.30,151); X,Y=np.meshgrid(xx,xx);Z=influence(X,Y)
    im=bx.imshow(np.log10(Z),origin='lower',extent=[0,.3,0,.3],cmap='viridis',aspect='auto',rasterized=True)
    bx.contour(X,Y,Z,levels=[.001,.01,.1],colors='white',linewidths=.6)
    bx.set(xlabel=r'$\delta_i$',ylabel=r'$\delta_j$',title=r'$\log_{10}\mathcal{B}(\delta_i,\delta_j)$')
    cb=fig.colorbar(im,cax=fig.add_axes([.425,.89,.23,.021]),orientation='horizontal');cb.ax.xaxis.set_ticks_position('top');cb.set_ticks([-4,-3,-2,-1,0]);cb.ax.tick_params(labelsize=7,pad=1)
    lengths=np.arange(2,9)
    for degree,color in zip([3,10,31],[BLUE,ORANGE,PURPLE]):
        lower=1-2*(degree-1)*influence(delta(lengths),delta(lengths))
        cx.plot(2*lengths,np.maximum(0,lower),'o-',ms=3,c=color,label=rf'$\Delta={degree}$')
    cx.axhline(.5,c='gray',ls='--',lw=.7)
    cx.set(xlabel=r'Decoration $n=2\ell$',ylabel='Certified coarse gap',ylim=(-.02,1.05),xticks=[4,8,12,16],title='Coarse-gap bound')
    cx.legend(fontsize=8,loc='lower right')
    panels([ax,bx,cx])
    finish(fig,'fig09_quantum_networks','Schematic core-wire architecture, exact two-port bound, and its homogeneous-degree coarse-gap consequence. Values below zero are displayed as zero (no positive certificate), not as a claim of a zero physical gap.',{'degrees':[3,10,31],'half_wire_lengths':lengths.tolist()})

def fig10():
    fig=plt.figure(figsize=(7.15,3.0))
    ax=fig.add_axes([.06,.17,.43,.71]); bx=fig.add_axes([.63,.22,.31,.61])
    vv=np.array([[0,0],[1,0],[.5,np.sqrt(3)/2]]);cent=vv.mean(axis=0)
    for i in range(3):
        region=np.array([vv[i],(vv[i]+vv[(i+1)%3])/2,cent,(vv[i]+vv[(i+2)%3])/2])
        ax.add_patch(Polygon(region,facecolor=COLORS[i],alpha=.22,edgecolor='white',lw=1.5))
        ax.text(*(.64*vv[i]+.36*cent),rf'$R_{i}$',ha='center',va='center',color=COLORS[i],fontsize=13)
        ax.text(*(vv[i]+.12*(vv[i]-cent)),rf'$p_{i}=1$',ha='center',va='center',fontsize=10)
    ax.add_patch(Polygon(vv,fill=False,edgecolor='black',lw=.7))
    ax.set(xlim=(-.15,1.15),ylim=(-.12,1),aspect='equal',title=r'$R_i=\{p_i=\max_j p_j\}$');ax.axis('off')
    mat=np.full((3,3),7/36);np.fill_diagonal(mat,11/18)
    bottom=np.zeros(3)
    for j in range(3):bx.bar(range(3),mat[j],bottom=bottom,color=COLORS[j],width=.60);bottom+=mat[j]
    bx.set(xticks=range(3),xticklabels=[r'$E_0$',r'$E_1$',r'$E_2$'],ylim=(0,1.04),ylabel='Eigenvalue',title='Noisy projective effects')
    bx.text(.5,.86,r'$\eta=5/12$',ha='center',transform=bx.transAxes,fontsize=12,bbox={'facecolor':'white','alpha':.9,'edgecolor':'none','pad':2})
    fig.text(.31,.095,r'$3\int_{R_i}P\,d\sigma=\frac{5}{12}P_i+\frac{7}{36}I$',ha='center',fontsize=11)
    panels([ax,bx])
    finish(fig,'fig10_measurement_cells','Exact Haar probability-simplex cells and their qutrit operator moments. Each output effect has eigenvalues 11/18,7/36,7/36.',{'visibility':'5/12','eigenvalues':['11/18','7/36','7/36']})

def fig11():
    fig=plt.figure(figsize=(7.15,3.1))
    ax=fig.add_axes([.07,.20,.25,.64]);bx=fig.add_axes([.41,.20,.25,.64]);cx=fig.add_axes([.76,.20,.20,.64])
    for a,title,power in [(ax,'Dipole: odd degree',1),(bx,'Quadrupole: even degree',2)]:
        x=np.linspace(-1,1,201);y=np.linspace(-1,1,201);X,Y=np.meshgrid(x,y);R=X*X+Y*Y
        Z=Y if power==1 else (3*Y**2-1)/2;Z=np.ma.masked_where(R>1,Z)
        a.imshow(Z,extent=[-1,1,-1,1],origin='lower',cmap='RdBu_r',vmin=-1,vmax=1,rasterized=True)
        a.add_patch(Circle((0,0),1,fill=False,edgecolor='black',lw=.7));a.axhline(0,color='white',lw=.5,alpha=.7)
        a.set(xticks=[],yticks=[],title=title,aspect='equal');a.set_frame_on(False)
        a.annotate('',xy=(0,.7),xytext=(0,-.7),arrowprops={'arrowstyle':'<->','lw':.8,'color':'black'})
    body=np.zeros((4,5));body[0,0]=1;body[1,1]=1;body[1,2]=1;body[2,2:5]=1;body[3,3:5]=1
    for i in range(4):
        for j in range(5):
            if body[i,j]:cx.scatter(j,i,s=42,c=ORANGE if j%2 else BLUE,marker='s')
    cx.set(xticks=range(5),yticks=range(4),xlabel='Total degree',ylabel='Body level',ylim=(-.4,3.5),xlim=(-.5,4.5),title='Body and degree')
    cx.text(.5,-.24,'blue: time-reversal even',ha='center',transform=cx.transAxes,fontsize=8)
    panels([ax,bx,cx])
    finish(fig,'fig11_multipoles','Exact spherical-harmonic restrictions n_z and (3 n_z^2-1)/2 on the unit disk. The spin-one degree/body diagram is truncated at degree4; each active site contributes degree1 or2. Time reversal removes odd total degree, not odd body level.')

def fig12():
    from scipy.special import beta as beta_function
    sys.path.insert(0,str(ROOT/'supplements/modular'))
    from positive_bessel_filters import exact_multiplier,build_rule,rule_multiplier
    fig=plt.figure(figsize=(7.15,3.5))
    axs=[fig.add_axes([x,.20,.24,.61]) for x in [.07,.395,.72]]
    u=np.linspace(.008,.992,500)
    for nu,color in zip([0,.5,2],[ORANGE,BLUE,PURPLE]):
        a=nu+.5; density=(u*(1-u))**(a-1)/beta_function(a,a)
        axs[0].plot(u,density,c=color,label=rf'$\nu={nu:g}$')
    axs[0].set(xlim=(0,1),ylim=(0,3.6),xlabel=r'Power $u$',ylabel='Beta density',title='Positive mixtures')
    axs[0].legend(fontsize=8,loc='upper center')
    x=np.linspace(0,5,400)
    for nu,color,label in [(-.5,ORANGE,'SLD'),(.5,BLUE,'BKM'),(2,PURPLE,r'$\nu=2$')]:
        axs[1].plot(x,exact_multiplier(x,nu),c=color,label=label)
    axs[1].axhline(1,c='gray',ls='--',lw=.7)
    axs[1].text(1.9,1.02,r'$\nu\to\infty$',fontsize=9)
    axs[1].set(xlabel=r'Modular half-frequency $x$',ylabel=r'$\phi_\nu(x)$',ylim=(0,1.13),title='Quantum score filters')
    axs[1].legend(fontsize=8,loc='upper right',bbox_to_anchor=(1,.91))
    xx=np.linspace(0,8,500);g=build_rule(.5,1,'gauss');r=build_rule(.5,1,'radau')
    exact=exact_multiplier(xx);upper=rule_multiplier(xx,g);lower=rule_multiplier(xx,r)
    axs[2].fill_between(xx,lower,upper,color=BLUE,alpha=.16)
    axs[2].semilogy(xx,upper,c=ORANGE,label='Gauss 1')
    axs[2].semilogy(xx,exact,c='black',lw=1,label='Exact')
    axs[2].semilogy(xx,lower,c=BLUE,label='Radau 1')
    axs[2].set(xlabel=r'$x$',ylabel='Multiplier',title='One-clock brackets',ylim=(1e-3,1.15))
    axs[2].legend(fontsize=8,loc='lower left')
    panels(axs)
    finish(fig,'fig12_information_clocks','Exact Bessel score family, beta mixture of operator means, and positive one-node Gaussian/Radau approximants. Shaded scalar spectral-multiplier bracket induces fixed-state information-matrix order, not CP-map order.',{'gauss_rule':g.to_json(),'radau_rule':r.to_json()})


def fig13():
    from scipy.special import gammaln
    sys.path.insert(0,str(ROOT/'supplements/probability'))
    from toric_assignment_certificate import compositions
    q,m=2,6
    alpha=np.asarray(list(compositions(m,q+1)),dtype=float)
    lattice=alpha/m
    points=(alpha+1)/(m+q+1)
    vertices=np.asarray([[0,0],[1,0],[.5,np.sqrt(3)/2]])
    axy=lattice@vertices;pxy=points@vertices
    fig=plt.figure(figsize=(7.15,3.55))
    ax=fig.add_axes([.045,.23,.265,.57]);bx=fig.add_axes([.395,.25,.23,.55]);cx=fig.add_axes([.73,.23,.24,.57])
    ax.plot([0,1,.5,0],[0,0,np.sqrt(3)/2,0],c='gray',lw=.6)
    for u,v in zip(axy,pxy):
        ax.annotate('',xy=v,xytext=u,arrowprops={'arrowstyle':'->','lw':.6,'color':'#7b7b7b','mutation_scale':5})
    ax.scatter(axy[:,0],axy[:,1],facecolors='white',edgecolors=BLUE,s=21,lw=.75,label='Exponent grid')
    ax.scatter(pxy[:,0],pxy[:,1],c=ORANGE,s=9,label='Squared moduli')
    ax.set(aspect='equal',xlim=(-.08,1.08),ylim=(-.10,.97),title='An exact matching')
    ax.axis('off');ax.legend(loc='upper center',bbox_to_anchor=(.5,-.015),fontsize=8,frameon=False)
    entropy=np.sum(np.where(lattice>0,lattice*np.log(np.maximum(lattice,1e-300)),0),axis=1)
    costs=entropy[:,None]-lattice@np.log(points).T
    im=bx.imshow(costs,cmap='viridis',origin='lower',aspect='equal',vmin=0,vmax=2.2,rasterized=True)
    bx.plot(np.arange(len(alpha)),np.arange(len(alpha)),c='white',lw=.7,alpha=.9)
    bx.set(xlabel='Squared-modulus point',ylabel='Exponent-grid point',title=r'Cost $D_{\rm KL}(a\Vert p)$',xticks=[0,13,27],yticks=[0,13,27])
    cax=fig.add_axes([.395,.855,.23,.023]);cb=fig.colorbar(im,cax=cax,orientation='horizontal');cb.set_ticks([0,1,2]);cb.ax.xaxis.set_ticks_position('top');cb.ax.tick_params(labelsize=8,pad=1)
    ks=np.arange(1,101)
    for q,color in [(1,BLUE),(2,ORANGE),(3,PURPLE)]:
        nn=np.array([math.comb((q+1)*int(k)+q,q) for k in ks],dtype=float)
        err=np.log(nn)/ks+gammaln(nn+1)/(ks*nn)
        cx.loglog(ks,err,c=color,label=rf'$q={q}$')
    cx.set(xlabel=r'Level $k$',ylabel='Guaranteed interval width',title='Vanishing error')
    cx.legend(loc='lower left',fontsize=8)
    panels([ax,bx,cx])
    finish(fig,'fig13_toric_transport','Exact finite assignment geometry for degree6 on CP2, deterministic rational squared-modulus points p=(alpha+1)/9, and the analytical angular-mean interval width log(N)/k+log(N!)/(kN). This concerns the angular mean, not each phase configuration or an attractive exponential moment.',{'degree':m,'dimension':2,'N':len(alpha),'point_rule':'p=(alpha+1)/(m+q+1)','assignment':'identity, certified by the monotonicity of log(alpha+1)','error_formula':'log(N)/k+log(N!)/(k*N)'})

if __name__=='__main__':
    requested=set(sys.argv[1:])
    for i,fun in enumerate([fig01,fig02,fig03,fig04,fig05,fig06,fig07,fig08,fig09,fig10,fig11,fig12,fig13],start=1):
        if not requested or f'{i:02d}' in requested:
            fun(); print(f'Generated figure {i:02d}',flush=True)
    path=ROOT/'data/figure_metadata.json'
    if path.exists():old=json.loads(path.read_text());old.update(META);META=old
    path.write_text(json.dumps(META,indent=2)+'\n')
