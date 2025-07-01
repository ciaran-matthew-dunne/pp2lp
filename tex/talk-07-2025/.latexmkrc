# Use lualatex for compilation
$pdf_mode = 4;  # 4 = lualatex
$dvi_mode = 0;
$postscript_mode = 0;

# Configure lualatex command (with synctex for editor integration)
$lualatex = 'lualatex -interaction=nonstopmode -synctex=1 %O %S';

# Use evince as PDF viewer
# $pdf_previewer = 'evince %S';

# Automatically open the PDF after compilation
# $preview_mode = 1;

# Optional: Use continuous preview mode (auto-recompile on changes)
# Uncomment the next line if you want this behavior
# $preview_continuous_mode = 1;

# Optional: Clean up auxiliary files
$clean_ext = 'synctex.gz run.xml';
