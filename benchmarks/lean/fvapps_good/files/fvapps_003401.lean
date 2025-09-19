-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def html (tag: String) (content: List String := []) (attrs: List (String × String) := []): String := sorry

theorem empty_tag_is_self_closing (tag: String) 
  (h: tag ≠ "") :
  html tag = s!"<{tag} />" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_content_wrapping (tag content: String)
  (h: tag ≠ "") :
  html tag [content] [] = s!"<{tag}>{content}</{tag}>" := sorry

theorem multiple_contents_newlines (tag: String) (contents: List String)
  (h1: tag ≠ "")
  (h2: contents.length ≥ 2) :
  html tag contents [] = String.intercalate "\n" 
    (contents.map (fun c => s!"<{tag}>{c}</{tag}>")) := sorry

theorem custom_attributes (tag key val: String) 
  (h1: tag ≠ "")
  (h2: key ≠ "cls")
  (h3: key ≠ "") 
  (h4: val ≠ "") :
  html tag [] [(key, val)] = s!"<{tag} {key}=\"{val}\" />" := sorry

theorem cls_becomes_class (tag val: String)
  (h1: tag ≠ "")
  (h2: val ≠ "") :
  html tag [] [("cls", val)] = s!"<{tag} class=\"{val}\" />" := sorry
-- </vc-theorems>