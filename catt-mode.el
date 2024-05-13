;; catt-mode.el -- CATT major emacs mode

(defvar catt-font-lock-keywords
 '(
   ("#.*" . 'font-lock-comment-face)
   ("\\<\\(let\\|coh\\|cylcoh\\|normalize\\|assert\\)\\>" . font-lock-keyword-face)
   ("\\<\\(U\\|Cat\\)\\>" . font-lock-builtin-face)
   ("\\<let[ \t]+\\([^ (=]*\\)" 1 'font-lock-function-name-face)
   ("\\<coh[ \t]+\\([^ (]*\\)" 1 'font-lock-function-name-face)
   ("\\<cylcoh[ \t]+\\([^ (]*\\)" 1 'font-lock-function-name-face)
  )
)

(defvar catt-mode-syntax-table
  (let ((st (make-syntax-table)))
    ;; Allow some extra characters in words
    (modify-syntax-entry ?_ "w" st)
    ;; Comments
    (modify-syntax-entry ?# "<" st)
    (modify-syntax-entry ?\n ">" st)
    st)
  "Syntax table for CATT major mode.")

(defvar catt-tab-width 4)
(defvar catt-mode-hook nil)
(defvar catt-mode-map nil "Keymap for catt-mode")

(progn
  (setq catt-mode-map (make-sparse-keymap))
  (define-key catt-mode-map (kbd "C-c C-c") `compile)
  )

(define-derived-mode catt-mode prog-mode
  "Catt" "Major mode for Catt files."
  :syntax-table catt-mode-syntax-table
  (set (make-local-variable 'comment-start) "#")
  (set (make-local-variable 'comment-start-skip) "#+\\s-*")
  (set (make-local-variable 'font-lock-defaults) '(catt-font-lock-keywords))
  (set (make-local-variable 'compile-command)
       (concat "catt " (shell-quote-argument buffer-file-name)))
  (use-local-map catt-mode-map)
  (setq mode-name "Catt")
  (run-hooks 'catt-mode-hook)
)


(provide 'catt-mode)

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.catt\\'" . catt-mode))
