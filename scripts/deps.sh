#!/usr/bin/env bash 
# scripts/deps.sh
# Sets up all dependencies required for McCarthy Lisp Explorer

# Detect OS
OS=$(uname)

echo "Detected OS: $OS"
echo "Required dependencies: coq, emacs, guile/guile3, pdfpc"
echo "Checking for dependencies instead of installing them..."

case "$OS" in
  FreeBSD)
    echo "For FreeBSD, you can install dependencies with:"
    echo "sudo pkg install -y coq emacs guile3 pdfpc"
    ;;
  Linux)
    if [ -f /etc/debian_version ]; then
      echo "For Debian/Ubuntu, you can install dependencies with:"
      echo "sudo apt-get update && sudo apt-get install -y coq emacs guile-3.0 pdfpc"
    elif [ -f /etc/fedora-release ]; then
      echo "For Fedora, you can install dependencies with:"
      echo "sudo dnf install -y coq emacs guile3 pdfpc"
    else
      echo "For your Linux distribution, please install the dependencies manually."
    fi
    ;;
  Darwin)
    echo "For macOS, you can install dependencies with:"
    echo "brew install coq emacs guile pdfpc"
    ;;
  *)
    echo "For your operating system, please install the dependencies manually."
    ;;
esac

# Verify installations
echo "Verifying installations..."

# Check Coq version - improved to handle FreeBSD's package structure
if command -v coqc >/dev/null 2>&1; then
  # Try with different options that avoid requiring the stdlib
  COQC_VERSION=$(coqc -boot -noinit -version 2>/dev/null || coqc --version 2>/dev/null || echo "Coq installed but version check failed")
  echo "Found Coq: $COQC_VERSION"
  
  # FreeBSD-specific check to ensure coqlib is properly set
  if [ "$OS" = "FreeBSD" ]; then
    COQLIB=$(pkg info -l coq | grep lib/coq$ | head -1)
    if [ -n "$COQLIB" ]; then
      echo "Coq library directory found at: $COQLIB"
      # Export this for the current session
      export COQLIB
      # Add a hint for users
      echo "You may want to add 'export COQLIB=$COQLIB' to your shell profile"
    else
      echo "WARNING: Could not find Coq library directory. You may need to set COQLIB manually."
    fi
  fi
else
  echo "ERROR: Could not find Coq installation"
  exit 1
fi

# Check Emacs version
if command -v emacs >/dev/null 2>&1; then
  EMACS_VERSION=$(emacs --version | head -n 1)
  echo "Found Emacs: $EMACS_VERSION"
  # Check if Emacs version is at least 30
  EMACS_MAJOR_VERSION=$(emacs --version | head -n 1 | grep -o '[0-9]\+' | head -n 1)
  if [ "$EMACS_MAJOR_VERSION" -lt 30 ]; then
    echo "WARNING: Emacs version is less than 30. Some features may not work correctly."
  fi
else
  echo "ERROR: Could not find Emacs installation"
  exit 1
fi

# Check Guile version
if command -v guile >/dev/null 2>&1; then
  GUILE_VERSION=$(guile --version | head -n 1)
  echo "Found Guile: $GUILE_VERSION"
  
  # FreeBSD often has both guile and guile3
  if [ "$OS" = "FreeBSD" ] && [ "${GUILE_VERSION#*2}" = "$GUILE_VERSION" ]; then
    # If version doesn't contain "2", try guile3
    if command -v guile3 >/dev/null 2>&1; then
      GUILE3_VERSION=$(guile3 --version | head -n 1)
      echo "Found Guile3: $GUILE3_VERSION"
    else
      echo "WARNING: Guile3 not found, but it was installed. Check your PATH."
    fi
  fi
else
  echo "ERROR: Could not find Guile installation"
  exit 1
fi

# Check PDF presenter console
if command -v pdfpc >/dev/null 2>&1; then
  PDFPC_VERSION=$(pdfpc --version | head -n 1)
  echo "Found PDFPC: $PDFPC_VERSION"
else
  echo "WARNING: Could not find PDFPC installation"
fi

echo "Environment setup complete"
