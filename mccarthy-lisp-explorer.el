;;; mccarthy-lisp-explorer.el --- Emacs configuration for McCarthy Lisp Explorer -*- lexical-binding: t -*-

;;; Commentary:
;; Project-specific Emacs configuration for Scheme development with
;; Geiser, Guile3, Org mode, TRAMP, and Paredit support.

;;; Code:

;; Package initialization
(require 'package)
(setq package-archives '(("melpa" . "https://melpa.org/packages/")
                         ("gnu" . "https://elpa.gnu.org/packages/")))
(package-initialize)

;; Ensure required packages are installed
(defvar mccarthy-required-packages
  '(geiser
    geiser-guile
    paredit
    org
    rainbow-delimiters))

(dolist (pkg mccarthy-required-packages)
  (unless (package-installed-p pkg)
    (package-refresh-contents)
    (package-install pkg)))

;; Project settings
(defvar mccarthy-project-root
  (file-name-directory (or load-file-name buffer-file-name))
  "Root directory of the McCarthy Lisp Explorer project.")

(defvar mccarthy-project-name "mccarthy-lisp-explorer"
  "Name of the McCarthy Lisp Explorer project.")

;; Geiser configuration for Guile
(require 'geiser)
(require 'geiser-guile)
(setq geiser-guile-binary "guile3")
(setq geiser-active-implementations '(guile))
(setq geiser-default-implementation 'guile)
(setq geiser-guile-load-path (list (expand-file-name "src" mccarthy-project-root)))

;; Paredit mode for structured editing
(require 'paredit)
(add-hook 'scheme-mode-hook #'paredit-mode)
(add-hook 'geiser-repl-mode-hook #'paredit-mode)
(add-hook 'emacs-lisp-mode-hook #'paredit-mode)

;; Rainbow delimiters for better parenthesis visibility
(require 'rainbow-delimiters)
(add-hook 'scheme-mode-hook #'rainbow-delimiters-mode)
(add-hook 'geiser-repl-mode-hook #'rainbow-delimiters-mode)
(add-hook 'emacs-lisp-mode-hook #'rainbow-delimiters-mode)

;; Org mode configuration for literate programming
(require 'org)
(org-babel-do-load-languages
 'org-babel-load-languages
 '((scheme . t)
   (emacs-lisp . t)
   (shell . t)))

;; Set up org-babel for Scheme
(setq org-babel-scheme-command "guile3")
(setq org-confirm-babel-evaluate nil)

;; TRAMP configuration (for remote development if needed)
(require 'tramp)
(setq tramp-default-method "ssh")

;; Project-specific key bindings
(global-set-key (kbd "C-c g r") 'geiser-mode)
(global-set-key (kbd "C-c g c") 'geiser-connect)
(global-set-key (kbd "C-c g e") 'geiser-eval-last-sexp)
(global-set-key (kbd "C-c g b") 'geiser-eval-buffer)
(global-set-key (kbd "C-c g d") 'geiser-doc-symbol-at-point)

;; File associations
(add-to-list 'auto-mode-alist '("\\.scm\\'" . scheme-mode))
(add-to-list 'auto-mode-alist '("\\.ss\\'" . scheme-mode))

;; Start Geiser REPL automatically for Scheme files in project
(defun mccarthy-setup-scheme-buffer ()
  "Setup Scheme buffer with project-specific configuration."
  (when (and (eq major-mode 'scheme-mode)
             (string-prefix-p mccarthy-project-root default-directory))
    (geiser-mode 1)
    (setq-local geiser-guile-load-path
                (list (expand-file-name "src" mccarthy-project-root)))))

(add-hook 'scheme-mode-hook #'mccarthy-setup-scheme-buffer)

;; Custom REPL startup
(defun mccarthy-start-repl ()
  "Start a Geiser REPL for the McCarthy Lisp Explorer project."
  (interactive)
  (let ((geiser-guile-load-path (list (expand-file-name "src" mccarthy-project-root))))
    (geiser 'guile)))

;; Display startup message
(message "McCarthy Lisp Explorer environment loaded from %s" mccarthy-project-root)

(provide 'mccarthy-lisp-explorer)
;;; mccarthy-lisp-explorer.el ends here