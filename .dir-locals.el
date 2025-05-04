;;; Directory Local Variables
;;; For more information see (info "(emacs) Directory Variables")

((nil . ((geiser-scheme-implementation . guile)
         (geiser-guile-binary . "guile3")
         (geiser-active-implementations . (guile))
         (geiser-implementations-alist . '(((regexp "\\.scm$") guile)))
         (eval . (progn
                   (unless (package-installed-p 'geiser)
                     (package-refresh-contents)
                     (package-install 'geiser))
                   (unless (package-installed-p 'geiser-guile)
                     (package-refresh-contents)
                     (package-install 'geiser-guile)))))))