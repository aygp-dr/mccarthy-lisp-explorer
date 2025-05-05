;;; mccarthy-lisp-explorer-coq.el --- Coq integration for McCarthy Lisp Explorer

;;; Commentary:
;; This file provides Coq integration for the McCarthy Lisp Explorer project.
;; It sets up Proof General and related tools for working with Coq proofs.

;;; Code:

;; Ensure package system is initialized
(require 'package)
(add-to-list 'package-archives '("melpa" . "https://melpa.org/packages/") t)
(package-initialize)

;; Install Proof General if not already installed
(unless (package-installed-p 'proof-general)
  (package-refresh-contents)
  (package-install 'proof-general))

;; Install Company-Coq for enhanced Coq experience
(unless (package-installed-p 'company-coq)
  (package-install 'company-coq))

;; Load and configure Proof General
(require 'proof-general)
(setq proof-three-window-mode-policy 'hybrid)  ;; Better window layout
(setq proof-script-fly-past-comments t)         ;; Skip comments when processing
(setq proof-splash-enable nil)                  ;; Disable splash screen

;; Configure Company-Coq
(add-hook 'coq-mode-hook #'company-coq-mode)

;; Set up keybindings for convenience
(with-eval-after-load 'proof-script
  (define-key proof-mode-map (kbd "C-c C-j") 'proof-goto-point)
  (define-key proof-mode-map (kbd "C-c C-,") 'proof-undo-last-successful-command))

;; Path to Coq executable - adjust as needed for your FreeBSD setup
(setq coq-prog-name "/usr/local/bin/coqtop")

;; Configure org-babel for Coq
(with-eval-after-load 'org
  (org-babel-do-load-languages
   'org-babel-load-languages
   '((coq . t))))

;; Integration with mccarthy-lisp-explorer.el
(with-eval-after-load 'mccarthy-lisp-explorer
  (message "Integrating Coq proofs with McCarthy Lisp Explorer"))

(provide 'mccarthy-lisp-explorer-coq)
;;; mccarthy-lisp-explorer-coq.el ends here
