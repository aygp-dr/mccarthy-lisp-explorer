;;; mccarthy-lisp-explorer.el --- Support for McCarthy Lisp exploration -*- lexical-binding: t; -*-

;; Author: Emacs User
;; Keywords: lisp, guile, scheme
;; Package-Requires: ((emacs "25.1") (geiser "0.16") (geiser-guile "0.16"))

;;; Commentary:
;; This package provides support for working with McCarthy's original Lisp
;; concepts in a modern Guile Scheme environment.
;;
;; Usage:
;;   (require 'mccarthy-lisp-explorer)
;;   (mccarthy-lisp-explorer-mode)

;;; Code:

(require 'geiser)
(require 'geiser-guile)

(defgroup mccarthy-lisp-explorer nil
  "Tools for exploring McCarthy's original Lisp concepts."
  :group 'lisp
  :prefix "mccarthy-lisp-explorer-")

(defcustom mccarthy-lisp-explorer-resources-dir "resources"
  "Directory containing resources such as McCarthy's papers."
  :type 'string
  :group 'mccarthy-lisp-explorer)

(defvar mccarthy-lisp-explorer-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "C-c C-m o") 'mccarthy-lisp-explorer-open-paper)
    (define-key map (kbd "C-c C-m e") 'mccarthy-lisp-explorer-eval-expression)
    (define-key map (kbd "C-c C-m i") 'mccarthy-lisp-explorer-insert-function)
    map)
  "Keymap for mccarthy-lisp-explorer-mode.")

(defun mccarthy-lisp-explorer-open-paper ()
  "Open McCarthy's original paper on recursive functions."
  (interactive)
  (let ((paper-path (expand-file-name "recursive.pdf" mccarthy-lisp-explorer-resources-dir)))
    (if (file-exists-p paper-path)
        (find-file paper-path)
      (message "Paper not found at %s. Run 'make resources/recursive.pdf' first." paper-path))))

(defun mccarthy-lisp-explorer-eval-expression (expr)
  "Evaluate a Lisp expression using Geiser.
EXPR is the expression to evaluate."
  (interactive "sEvaluate expression: ")
  (geiser-eval-region (point) (point) expr))

(defun mccarthy-lisp-explorer-insert-function (func-name)
  "Insert a template for a primitive McCarthy Lisp function.
FUNC-NAME is the name of the function to insert."
  (interactive "sFunction name: ")
  (let ((template (format "(define (%s . args)
  ;; Implementation of %s
  )" func-name func-name)))
    (insert template)))

(defun mccarthy-lisp-explorer-setup-geiser ()
  "Set up Geiser for McCarthy Lisp exploration."
  (when (and (featurep 'geiser) (featurep 'geiser-guile))
    (setq-local geiser-guile-binary "guile3")
    (setq-local geiser-active-implementations '(guile))))

;;;###autoload
(define-minor-mode mccarthy-lisp-explorer-mode
  "Minor mode for exploring McCarthy's original Lisp concepts."
  :lighter " McCarthyLisp"
  :keymap mccarthy-lisp-explorer-mode-map
  (mccarthy-lisp-explorer-setup-geiser))

(provide 'mccarthy-lisp-explorer)
;;; mccarthy-lisp-explorer.el ends here