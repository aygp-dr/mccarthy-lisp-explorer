# For installing Coq and dependencies
sudo pkg install -y coq opam emacs-devel guile3

# Initialize OPAM if not already done
if [ ! -d ~/.opam ]; then
  opam init --disable-sandboxing -y
  eval `opam env`
fi

# Install Coq standard library
opam install coq-stdlib

# Setup XDG Base Directory Specification for Emacs and Guile3
# Check if XDG directories exist, if not create them
if [ ! -d "$XDG_CONFIG_HOME" ]; then
  XDG_CONFIG_HOME=${XDG_CONFIG_HOME:-$HOME/.config}
  echo "Setting up XDG_CONFIG_HOME: $XDG_CONFIG_HOME"
  mkdir -p "$XDG_CONFIG_HOME"
fi

if [ ! -d "$XDG_DATA_HOME" ]; then
  XDG_DATA_HOME=${XDG_DATA_HOME:-$HOME/.local/share}
  echo "Setting up XDG_DATA_HOME: $XDG_DATA_HOME"
  mkdir -p "$XDG_DATA_HOME"
fi

if [ ! -d "$XDG_CACHE_HOME" ]; then
  XDG_CACHE_HOME=${XDG_CACHE_HOME:-$HOME/.cache}
  echo "Setting up XDG_CACHE_HOME: $XDG_CACHE_HOME"
  mkdir -p "$XDG_CACHE_HOME"
fi

# Create Emacs XDG config directory if it doesn't exist
EMACS_CONFIG_DIR="$XDG_CONFIG_HOME/emacs"
if [ ! -d "$EMACS_CONFIG_DIR" ]; then
  echo "Creating Emacs XDG config directory: $EMACS_CONFIG_DIR"
  mkdir -p "$EMACS_CONFIG_DIR"
fi

# Create Guile XDG config directory if it doesn't exist
GUILE_CONFIG_DIR="$XDG_CONFIG_HOME/guile"
if [ ! -d "$GUILE_CONFIG_DIR" ]; then
  echo "Creating Guile XDG config directory: $GUILE_CONFIG_DIR"
  mkdir -p "$GUILE_CONFIG_DIR"
fi

# Add Guile load path
echo "export GUILE_LOAD_PATH=\"$(pwd)/src:\$GUILE_LOAD_PATH\"" >> "$XDG_CONFIG_HOME/guile/env"

# Print Coq paths for troubleshooting
echo "Coq installation directory: $(coqc -where)"
echo "XDG_CONFIG_HOME: $XDG_CONFIG_HOME"
echo "Emacs XDG config: $EMACS_CONFIG_DIR"
echo "Guile XDG config: $GUILE_CONFIG_DIR"
