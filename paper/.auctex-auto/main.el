(TeX-add-style-hook
 "main"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("scrbook" "headsepline" "footsepline" "footinclude=false" "oneside" "fontsize=11pt" "paper=a4" "listof=totoc" "bibliography=totoc")))
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("nag" "l2tabu" "orthodox")))
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "path")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "url")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "nolinkurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperbaseurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperimage")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperref")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "href")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "path")
   (TeX-run-style-hooks
    "latex2e"
    "settings"
    "pages/cover"
    "pages/title"
    "pages/disclaimer"
    "pages/acknowledgments"
    "pages/abstract"
    "chapters/indexing_methods"
    "nag"
    "scrbook"
    "scrbook10")
   (TeX-add-symbols
    "getUniversity"
    "getFaculty"
    "getTitle"
    "getTitleGer"
    "getAuthor"
    "getDoctype"
    "getSupervisor"
    "getAdvisor"
    "getSubmissionDate"
    "getSubmissionLocation"))
 :latex)

