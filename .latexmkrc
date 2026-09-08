# Where biber is allowed to keep its unpacked self.
#
# biber is not an ordinary program: it is a PAR::Packer executable, a Perl
# interpreter and its whole library packed into one file, which unpacks itself
# into a cache directory on first run and reuses it afterwards. The default
# location is $TMPDIR, and on macOS that is under /var/folders, which the system
# sweeps periodically. A partly swept cache is worse than a missing one — biber
# cannot find its own Unicode tables, dies without printing an error, exits 25,
# and leaves a zero-byte main.bbl behind.
#
# Nothing about that failure points at biber. LaTeX compiles perfectly happily
# against an empty bibliography, so main.log is clean and the only symptom is
# the editor saying the recipe failed; and html/rebuild.sh will build the whole
# site against that empty file, quietly replacing every citation in the book
# with nothing. It has happened once, on 2026-09-07.
#
# Pinning the cache under ~/.cache, which nothing sweeps, is the entire fix.
#
# This lives in the repository root rather than in html/rebuild.sh because
# latexmk reads it whoever starts it — the site build, the editor's build
# recipe, or latexmk run by hand — and all three call biber.
use File::Path qw(make_path);
my $par_cache = "$ENV{HOME}/.cache/par";
make_path($par_cache) unless -d $par_cache;
$ENV{PAR_GLOBAL_TMPDIR} = $par_cache;

# If it ever does break again, the fix is to delete that directory: biber
# unpacks itself again on the next run, which costs a few seconds once.
