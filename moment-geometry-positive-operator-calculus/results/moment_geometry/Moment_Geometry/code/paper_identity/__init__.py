"""Reusable visual grammar for the supplied scientific-figure references."""
from .style import (
    RC, TIME_STOPS, PHASE_STOPS, INK, BLUE, PINK, GROUP_CYAN, GROUP_ROSE,
    apply_style, style_context, px, paper_figure, add_axes_px, text_px,
    time_cmap, phase_cmap, top_colorbar, panel_font, panel_label, gradient_line,
    phase_image, direction_field, interaction_disk, rounded_group,
    scaling_guide, export,
)

__version__ = "1.0.0"

from .surface import SurfaceInset, gaussian_surface, add_surface_inset, build_surface_demo
