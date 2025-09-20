-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_audio (s : String) : Bool := sorry
def is_image (s : String) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem valid_audio_files (name : String) (ext : String) 
  (h1 : ∀ c ∈ name.data, c.isAlpha)
  (h2 : ext ∈ ["mp3", "flac", "alac", "aac"]) :
  is_audio (name ++ "." ++ ext) = true := 
sorry

theorem valid_image_files (name : String) (ext : String)
  (h1 : ∀ c ∈ name.data, c.isAlpha) 
  (h2 : ext ∈ ["jpg", "jpeg", "png", "bmp", "gif"]) :
  is_image (name ++ "." ++ ext) = true :=
sorry

theorem invalid_uppercase_audio_extensions (name : String) (ext : String)
  (h1 : ∀ c ∈ name.data, c.isAlpha)
  (h2 : ext ∈ ["MP3", "FLAC", "ALAC", "AAC"]) :
  is_audio (name ++ "." ++ ext) = false :=
sorry

theorem invalid_uppercase_image_extensions (name : String) (ext : String) 
  (h1 : ∀ c ∈ name.data, c.isAlpha)
  (h2 : ext ∈ ["JPG", "PNG", "BMP", "GIF"]) :
  is_image (name ++ "." ++ ext) = false :=
sorry

theorem invalid_filenames (name : String)
  (h : ∃ c ∈ name.data, c.isDigit ∨ c = '!' ∨ c = '@' ∨ c = '#' ∨ c = '$' ∨ 
       c = '%' ∨ c = '^' ∨ c = '&' ∨ c = '*' ∨ c = '(' ∨ c = ')' ∨ 
       c = '_' ∨ c = ' ') :
  (is_audio (name ++ ".mp3") = false) ∧ 
  (is_image (name ++ ".jpg") = false) :=
sorry

theorem invalid_extensions (name : String)
  (h : ∀ c ∈ name.data, c.isAlpha) :
  (is_audio (name ++ ".txt") = false) ∧ 
  (is_image (name ++ ".doc") = false) :=
sorry

theorem empty_or_malformed (s : String)
  (h : s.isEmpty ∨ ¬ ('.' ∈ s.data)) :
  (is_audio s = false) ∧ (is_image s = false) :=
sorry
-- </vc-theorems>