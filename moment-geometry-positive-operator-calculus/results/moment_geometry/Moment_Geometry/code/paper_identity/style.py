"""Computer Modern, thin-frame scientific figure grammar measured from seven refs.

All helpers that end in ``_px`` use a top-left pixel coordinate system at the
figure's creation DPI. Ordinary Matplotlib sizes remain points. The figures can
then be exported at any DPI without changing the physical layout.
"""
from contextlib import contextmanager
from pathlib import Path

import matplotlib as mpl
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.colors import LinearSegmentedColormap, Normalize
from matplotlib.collections import LineCollection
from matplotlib.patches import Circle, Wedge, FancyArrowPatch, FancyBboxPatch
from matplotlib.ticker import FuncFormatter
from matplotlib.font_manager import FontProperties


TIME_STOPS = ["#9e0142", "#d53e4f", "#f46d43", "#fdae61", "#fee08b",
              "#abdda4", "#66c2a5", "#3288bd", "#5e4fa2"]
PHASE_STOPS = ["#000000", "#0000ff", "#008000", "#ffa500", "#ff0000", "#000000"]
INK = "#000000"
BLUE = "#0077b5"
PINK = "#e377c2"
GROUP_CYAN = "#d9ecec"
GROUP_ROSE = "#ffe7e3"

RC = {
    "font.family": "serif", "font.serif": ["cmr10", "DejaVu Serif"],
    "font.size": 14.4, "mathtext.fontset": "cm", "text.usetex": False,
    "axes.formatter.use_mathtext": True, "axes.unicode_minus": False,
    "axes.linewidth": 0.6, "axes.labelsize": 24, "axes.labelpad": 3,
    "axes.grid": False, "axes.facecolor": "white", "figure.facecolor": "white",
    "savefig.facecolor": "white", "savefig.transparent": False,
    "savefig.bbox": None,
    "xtick.direction": "in", "ytick.direction": "in",
    "xtick.labelsize": 14.4, "ytick.labelsize": 14.4,
    "xtick.major.size": 3.0, "ytick.major.size": 3.0,
    "xtick.major.width": 0.6, "ytick.major.width": 0.6,
    "xtick.minor.size": 1.8, "ytick.minor.size": 1.8,
    "xtick.minor.width": 0.55, "ytick.minor.width": 0.55,
    "xtick.major.pad": 3.0, "ytick.major.pad": 3.0,
    "lines.linewidth": 1.1, "lines.solid_capstyle": "round",
    "lines.dash_capstyle": "butt", "legend.frameon": False,
    "figure.dpi": 150, "savefig.dpi": 150,
    "image.interpolation": "bilinear", "image.origin": "lower",
    "svg.fonttype": "path", "pdf.fonttype": 42, "ps.fonttype": 42,
    "path.simplify": False, "figure.max_open_warning": 30,
}


def apply_style():
    """Apply the kit's publication style globally; use style_context to isolate it."""
    mpl.rcParams.update(RC)


@contextmanager
def style_context(**overrides):
    """Temporarily apply the identity, optionally overriding rcParams."""
    with mpl.rc_context({**RC, **overrides}):
        yield


def px(value, dpi=150):
    """Convert design pixels to points, for fontsize/linewidth/markersize."""
    return np.asarray(value) * 72.0 / dpi


def paper_figure(width_px, height_px, dpi=150):
    fig = plt.figure(figsize=(width_px / dpi, height_px / dpi), dpi=dpi,
                     layout=None, facecolor="white")
    fig._identity_design_size = (float(width_px), float(height_px))
    fig._identity_design_dpi = float(dpi)
    return fig


def design_size(fig):
    return getattr(fig, "_identity_design_size", tuple(fig.get_size_inches()*fig.dpi))


def add_axes_px(fig, rect, **kwargs):
    """Add an Axes using [left, top, width, height] in design pixels."""
    w, h = design_size(fig)
    x, y, aw, ah = rect
    return fig.add_axes([x/w, 1-(y+ah)/h, aw/w, ah/h], **kwargs)


def text_px(fig, x, y, text, size=30, **kwargs):
    """Place figure text using top-origin pixels; y is the anchor, not glyph top."""
    w, h = design_size(fig)
    dpi = getattr(fig, "_identity_design_dpi", fig.dpi)
    opts = {"fontsize": px(size, dpi), "va": "center", "ha": "left"}
    opts.update(kwargs)
    return fig.text(x/w, 1-y/h, text, **opts)


def time_cmap():
    """Nine-stop Spectral derivative; deliberately omits two pale center stops."""
    return LinearSegmentedColormap.from_list("paper_time", TIME_STOPS, N=256)


def phase_cmap(kind="half"):
    """half: white to pure blue; cycle: black-blue-green-orange-red-black."""
    if kind == "half":
        return LinearSegmentedColormap.from_list("paper_half_phase", ["white", "blue"], N=256)
    if kind == "cycle":
        return LinearSegmentedColormap.from_list("paper_cycle_phase", PHASE_STOPS, N=256)
    if kind == "diverging":
        return mpl.colormaps["berlin"]
    raise ValueError("kind must be 'half', 'cycle', or 'diverging'")


def top_colorbar(fig, rect, cmap, norm=None, ticks=(0, .5, 1),
                 ticklabels=None, label=None, label_y=None,
                 label_size=50, tick_size=27, tick_direction="in"):
    """A separately positioned, slim horizontal colorbar with ticks above.

    rect is [left, top, width, height] in design pixels. Explicit normalization
    is shared by the plotted artists and colorbar; defaults to Normalize(0,1).
    """
    ax = add_axes_px(fig, rect)
    norm = Normalize(0, 1) if norm is None else norm
    bar = fig.colorbar(mpl.cm.ScalarMappable(norm=norm, cmap=cmap), cax=ax,
                      orientation="horizontal", ticks=ticks)
    bar.ax.xaxis.set_ticks_position("top")
    bar.ax.xaxis.set_label_position("top")
    dpi = getattr(fig, "_identity_design_dpi", fig.dpi)
    bar.ax.tick_params(labelsize=px(tick_size, dpi), direction=tick_direction,
                       length=px(5, dpi), width=px(1, dpi), pad=px(6, dpi))
    bar.outline.set_linewidth(px(1.1, dpi))
    if ticklabels is not None:
        bar.ax.set_xticklabels(ticklabels)
    if label:
        text_px(fig, rect[0]+rect[2]/2,
                rect[1]-65 if label_y is None else label_y,
                label, size=label_size, ha="center")
    return bar


def panel_font(size=32, weight="normal", dpi=150):
    """Bundled Latin Modern-derived italic with portable TrueType PDF embedding."""
    filename = "paperpanel-bolditalic.ttf" if weight == "bold" else "paperpanel-italic.ttf"
    return FontProperties(fname=Path(__file__).parent/"fonts"/filename,
                          size=px(size, dpi))


def panel_label(ax, letter, xy=(.035, .96), size=32, color="black", weight="normal", **kwargs):
    """Italic, parenthesized panel marker, anchored inside an Axes."""
    dpi = getattr(ax.figure, "_identity_design_dpi", ax.figure.dpi)
    defaults = dict(transform=ax.transAxes, va="top", ha="left",
                    fontproperties=panel_font(size, weight=weight, dpi=dpi), color=color, zorder=20)
    defaults.update(kwargs)
    return ax.text(*xy, f"({letter})", **defaults)


def gradient_line(ax, x, y, values, *, cmap=None, norm=None, linewidth=1.5,
                  **kwargs):
    """Draw a continuous colored path without hairline gaps at segment joins.

    x, y, values must have equal lengths. linewidth is in Matplotlib points.
    NaN-separated fragments are supported and retain their original colors.
    The returned LineCollection is itself a colorbar-compatible mappable.
    """
    x, y, c = (np.asarray(a, dtype=float) for a in (x, y, values))
    if not (x.ndim == y.ndim == c.ndim == 1 and len(x) == len(y) == len(c)):
        raise ValueError("x, y and values must be equal-length 1D arrays")
    if len(x) < 2:
        raise ValueError("At least two points are required")
    p = np.column_stack((x, y))
    finite = np.isfinite(p).all(axis=1) & np.isfinite(c)
    indices = np.flatnonzero(finite)
    runs = np.split(indices, np.flatnonzero(np.diff(indices) != 1)+1)
    segments, colors = [], []
    for run in runs:
        if len(run) < 2:
            continue
        points = p[run]
        mids = .5 * (points[:-1] + points[1:])
        left = np.vstack((points[:1], mids))
        right = np.vstack((mids, points[-1:]))
        segments.append(np.stack((left, points, right), axis=1))
        colors.append(c[run])
    if not segments:
        raise ValueError("No finite line segments")
    seg, color_values = np.concatenate(segments), np.concatenate(colors)
    if norm is None:
        norm = Normalize(float(color_values.min()), float(color_values.max()))
    lc = LineCollection(seg, array=color_values, cmap=time_cmap() if cmap is None else cmap,
                        norm=norm, linewidths=linewidth, capstyle="round", **kwargs)
    ax.add_collection(lc)
    ax.update_datalim(p[np.isfinite(p).all(axis=1)])
    ax.autoscale_view()
    return lc


def phase_image(ax, theta, extent, *, full_cycle=False, **kwargs):
    """Map a scalar angle field to the reference palettes, with fixed normalization."""
    vmax = 2*np.pi if full_cycle else np.pi/2
    opts = dict(cmap=phase_cmap("cycle" if full_cycle else "half"),
                vmin=0, vmax=vmax, extent=extent, origin="lower",
                interpolation="bilinear", aspect="auto")
    opts.update(kwargs)
    return ax.imshow(theta, **opts)


def direction_field(ax, x, y, theta, length=.07, *, cmap=None, norm=None,
                    width=.004, alpha=1., **kwargs):
    """Unit-direction arrows; angles in radians, length in axis data coordinates."""
    u, v = length*np.cos(theta), length*np.sin(theta)
    opts = dict(angles="xy", scale_units="xy", scale=1, pivot="tail",
                width=width, headwidth=3.6, headlength=4.5, headaxislength=4,
                alpha=alpha)
    opts.update(kwargs)
    if cmap is None:
        return ax.quiver(x, y, u, v, **opts)
    return ax.quiver(x, y, u, v, theta, cmap=cmap, norm=norm, **opts)


def interaction_disk(ax, center=(0, 0), radius=1, *, color="#1f77b4",
                     heading=0, aperture=360, offset=(0, 0), core_radius=.5,
                     alpha=.14, dashed_original=False, arrow_length=.65):
    """Circle / hard sector / displaced soft interaction kernel and center arrow."""
    x, y = center
    ox, oy = offset
    if dashed_original:
        ax.add_patch(Circle(center, radius, facecolor="none", edgecolor=".4",
                            linewidth=.6, linestyle=(0, (3, 3))))
    center_shifted = (x+ox, y+oy)
    if aperture >= 360:
        area = Circle(center_shifted, radius)
    else:
        a = np.degrees(heading)
        area = Wedge(center_shifted, radius, a-aperture/2, a+aperture/2)
    area.set_facecolor(mpl.colors.to_rgba(color, alpha))
    area.set_edgecolor(color)
    area.set_linewidth(.75)
    ax.add_patch(area)
    ax.add_patch(Circle(center, core_radius*radius, facecolor="#cccccc", edgecolor="none"))
    endpoint = (x+arrow_length*radius*np.cos(heading), y+arrow_length*radius*np.sin(heading))
    start = (x-.3*radius*np.cos(heading), y-.3*radius*np.sin(heading))
    arrow = FancyArrowPatch(start, endpoint, arrowstyle="-|>", mutation_scale=13,
                            linewidth=1.2, color=color)
    ax.add_patch(arrow)
    ax.set_aspect("equal")
    return area, arrow


def rounded_group(fig, rect, color, radius_px=14):
    """Soft rounded figure-level band behind a panel group, in design pixels."""
    w, h = design_size(fig)
    x, y, bw, bh = rect
    box = FancyBboxPatch((x/w, 1-(y+bh)/h), bw/w, bh/h,
                         boxstyle=f"round,pad=0,rounding_size={radius_px/w}",
                         transform=fig.transFigure, facecolor=color, linewidth=0,
                         mutation_aspect=w/h, zorder=-10)
    fig.add_artist(box)
    return box


def scaling_guide(ax, xspan, anchor, exponent, *, label=None, label_xy=None,
                  linestyle="-", linewidth=1.2, **kwargs):
    """Plot y=y0*(x/x0)**exponent on log axes; all values are data coordinates."""
    x = np.geomspace(*xspan, 100)
    x0, y0 = anchor
    if min(*xspan, x0, y0) <= 0:
        raise ValueError("Scaling-guide coordinates must be positive")
    line, = ax.plot(x, y0*(x/x0)**exponent, color="black", linestyle=linestyle,
                    linewidth=linewidth, **kwargs)
    if label:
        ax.text(*(label_xy or (x[-1], y0*(x[-1]/x0)**exponent)), label)
    return line


def export(fig, stem, formats=("png", "pdf", "svg"), dpi=150):
    """Export exact-layout artwork; intentionally avoid bbox_inches='tight'."""
    stem = Path(stem)
    stem.parent.mkdir(parents=True, exist_ok=True)
    paths = []
    for fmt in formats:
        dest = stem.with_suffix("."+fmt)
        with mpl.rc_context({"savefig.bbox": None}):
            fig.savefig(dest, dpi=dpi, facecolor="white", bbox_inches=None,
                        metadata={"Creator": "Matplotlib visual identity kit"} if fmt == "pdf" else None)
        paths.append(dest)
    return paths
