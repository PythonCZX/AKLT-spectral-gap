"""A Matplotlib-only shaded 3-D inset with a visible level-set construction.

The inset uses real grid geometry, not an image pasted from a renderer.  For
custom data pass either 1-D x/y coordinates or meshgrids X/Y together with Z.
The dense surface can be rasterized for small PDF/SVG files; the plane,
level curve and summit marker remain vector artists.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Any
import numpy as np
from matplotlib import colormaps
from matplotlib.colors import LightSource

@dataclass
class SurfaceInset:
    """Axes and artists, returned so callers can adjust a finished inset."""
    axes: Any
    surface: Any
    plane: Any
    level_curve: Any
    summit: Any


def gaussian_surface(n: int = 100, sigma: float = 0.58):
    """Return a smooth reference-style hill as ``X, Y, Z`` arrays."""
    xy = np.linspace(-1.55, 1.55, n)
    X, Y = np.meshgrid(xy, xy)
    Z = np.exp(-(X**2 + Y**2)/(2 * sigma**2))
    return X, Y, Z


def add_surface_inset(parent, bounds=(0.48, 0.59, 0.52, 0.40), *,
                      X=None, Y=None, Z=None, level=0.52,
                      elev=24, azim=-65, box_aspect=(1, 1, 0.72),
                      plane_color='#ed6969', plane_alpha=0.19,
                      contour_color='red', contour_width=1.05,
                      light_azimuth=315, light_altitude=38,
                      mark_summit=True, rasterized=True,
                      projection='ortho', zoom=1.30):
    """Add a gray, shaded height field and its horizontal level-set plane.

    Parameters
    ----------
    parent : matplotlib.axes.Axes
        The 2-D host panel. ``bounds`` are fractions of this panel, not pixels.
    bounds : (left, bottom, width, height)
        Placement inside the parent axes. These are axes-relative coordinates.
    X, Y, Z : array-like, optional
        Coordinates and surface heights. X/Y may be 1-D or matching 2-D grids.
        Supplying none creates the illustrative Gaussian from the reference.
        All three are required for custom data, with finite heights and at
        least two rows/columns. Regular rectilinear grids give best shading.
    level : float
        Height of the plane and the red intersection contour, in Z units.
    rasterized : bool
        Rasterize only the dense surface collection on vector export.
        PNG exports always rasterize the entire figure, by definition.

    Returns
    -------
    SurfaceInset
        The mplot3d axes plus editable surface, plane, contour and marker.

    Notes
    -----
    mplot3d sorts polygons; transparency is not physically ray-traced.  A
    modest viewing angle, single-valued height field and thin plane give the
    clean reference appearance. The plane is a contour polygon with a hole around the upper hill, avoiding tinting
    exposed geometry. The level curve is drawn above the shaded
    surface to keep the scientific construction legible at small inset size.
    The full sampling grid is retained, with antialiasing off to avoid mesh
    seams. A larger grid increases PDF/SVG size unless rasterized=True.
    """
    supplied = (X is not None, Y is not None, Z is not None)
    if not any(supplied):
        X, Y, Z = gaussian_surface()
    elif not all(supplied):
        raise ValueError('For custom data, provide X, Y and Z together.')
    X, Y, Z = map(lambda a: np.asarray(a, dtype=float), (X,Y,Z))
    if X.ndim == Y.ndim == 1:
        X, Y = np.meshgrid(X, Y)
    if X.shape != Y.shape or X.shape != Z.shape or Z.ndim != 2:
        raise ValueError('X, Y and Z must have the same 2-D grid shape.')
    if min(Z.shape) < 2 or not all(np.isfinite(v).all() for v in (X,Y,Z)):
        raise ValueError('Surface grids need at least 2 x 2 finite samples.')
    zmin, zmax = float(Z.min()), float(Z.max())
    if not zmin < level < zmax:
        raise ValueError('level must lie strictly inside the range of Z.')
    ax = parent.inset_axes(bounds, projection='3d', computed_zorder=False)
    ax.set_proj_type(projection)
    ax.view_init(elev=elev, azim=azim)
    ax.set_box_aspect(box_aspect, zoom=zoom)
    ax.set_axis_off()
    ax.patch.set_alpha(0)
    ax.set_facecolor('none')
    # A bounded gray field avoids black shadows while preserving the hill.
    dy, dx = np.mean(np.diff(Y[:,0])), np.mean(np.diff(X[0]))
    dx, dy = abs(float(dx)) or 1., abs(float(dy)) or 1.
    lights = LightSource(azdeg=light_azimuth, altdeg=light_altitude)
    gray = np.ones((*Z.shape,3)) * .68
    colors = lights.shade_rgb(gray, Z, vert_exag=.72, dx=dx, dy=dy,
                             fraction=1.15, blend_mode='soft')
    surface = ax.plot_surface(X,Y,Z, rstride=1,cstride=1,facecolors=colors,
                              linewidth=0,antialiased=False,shade=False,
                              rasterized=rasterized,zorder=1)
    # Draw the plane as one contour polygon with a hole around the upper
    # hill. This avoids both tinting exposed geometry and alpha accumulation
    # at thousands of shared mesh edges. contourf projects the real grid's
    # sublevel region onto a horizontal plane at the requested height.
    plane = ax.contourf(X,Y,Z,levels=[zmin-1e-9*(zmax-zmin),level],
                        zdir='z',offset=level,colors=[plane_color],
                        alpha=plane_alpha,antialiased=True,zorder=2)
    curve = ax.contour(X,Y,Z,levels=[level],zdir='z',offset=level,
                       colors=[contour_color],linewidths=contour_width,
                       zorder=3)
    peak = None
    if mark_summit:
        iy, ix = np.unravel_index(np.argmax(Z),Z.shape)
        peak = ax.scatter([X[iy,ix]],[Y[iy,ix]],[zmax+.075*(zmax-zmin)],
                          c='black',marker='*',s=28,depthshade=False,zorder=4)
    ax.set(xlim=(X.min(),X.max()),ylim=(Y.min(),Y.max()),
           zlim=(zmin-.04*(zmax-zmin),zmax+.10*(zmax-zmin)))
    return SurfaceInset(ax,surface,plane,curve,peak)


def build_surface_demo():
    """Return a large editable example that exposes the 3-D construction.

    The two panels show exactly the same height-field and level, once in 3-D
    and once as a plan-view contour.  This is also a small, useful integration
    example for supplying data instead of using the default Gaussian.
    """
    import matplotlib.pyplot as plt
    from paper_identity.style import style_context
    with style_context():
        fig = plt.figure(figsize=(8.2,3.9),dpi=150)
        host = fig.add_axes([.015,.05,.52,.84])
        host.set_axis_off()
        X,Y,Z=gaussian_surface(n=140,sigma=.58)
        inset=add_surface_inset(host,bounds=(0,0,1,1),X=X,Y=Y,Z=Z,
                               level=.56,elev=22,azim=-65,zoom=1.05,
                               contour_width=1.3)
        fig.text(.28,.95,'Shaded height field',ha='center',va='top',fontsize=17)
        ax=fig.add_axes([.63,.18,.31,.64])
        ax.contourf(X,Y,Z,levels=np.linspace(0,1,18),cmap='Greys_r')
        ax.contour(X,Y,Z,levels=[.56],colors='red',linewidths=1.3)
        ax.plot([0],[0],'k*',markersize=8)
        ax.set(aspect='equal',xlim=(-1.55,1.55),ylim=(-1.55,1.55),
               xticks=[-1,0,1],yticks=[-1,0,1])
        ax.set_xlabel('$x/L$',fontsize=19)
        ax.set_ylabel('$y/L$',fontsize=19)
        fig.text(.785,.95,'The same level in plan view',ha='center',va='top',fontsize=17)
        fig.text(.27,.045,'Gray surface + translucent plane + red intersection',
                 ha='center',fontsize=10.5)
        return fig
