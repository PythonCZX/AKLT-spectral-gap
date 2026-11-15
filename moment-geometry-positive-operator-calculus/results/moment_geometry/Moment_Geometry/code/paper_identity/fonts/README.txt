Panel font portability
======================

The original Latin Modern OTF files are retained unchanged, with their license.
The plotting helper loads renamed TrueType derivatives: paperpanel-italic.ttf
and paperpanel-bolditalic.ttf. Their shape and advance widths are retained;
cubic outlines are approximated with quadratic outlines at a maximum error of
one font unit. This avoids Matplotlib embedding a CFF OpenType font as a PDF
TrueType font. The final PDF font table was checked after this change.

See DERIVED-FONT-NOTICE.txt for attribution, changes, and maintenance status.
