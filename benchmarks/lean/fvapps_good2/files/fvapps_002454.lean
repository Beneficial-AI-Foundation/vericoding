-- <vc-preamble>
def split_lines (s : String) : List String :=
  s.splitOn "\n"
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def parse_html (s : String) : String :=
  sorry

def is_lowercase_letter (c : Char) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_tag_parse {tag : String}
  (h : ∀ c, c ∈ tag.data → is_lowercase_letter c) :
  parse_html s!"<{tag}>" = tag :=
sorry

theorem tag_with_attrs_parse {tag : String} {attrs : List (String × String)}
  (h1 : ∀ c, c ∈ tag.data → is_lowercase_letter c)
  (h2 : ∀ (k v : String), (k, v) ∈ attrs → ∀ c, c ∈ k.data → is_lowercase_letter c) :
  let attr_str := String.join (attrs.map (fun (k,v) => s!"{k}=\"{v}\""))
  let html := s!"<{tag} {attr_str}>"
  let result := split_lines (parse_html html)
  result[0]! = tag ∧
  (∀ i k v, attrs[i]! = (k,v) → result[i+1]! = s!"-> {k} > {v}") :=
sorry

theorem multiple_tags_parse {tags : List String} {attrs_list : List (List (String × String))}
  (h1 : tags.length > 0)
  (h2 : attrs_list.length = tags.length)
  (h3 : ∀ tag, tag ∈ tags → ∀ c, c ∈ tag.data → is_lowercase_letter c)
  (h4 : ∀ attrs, attrs ∈ attrs_list → ∀ k v, (k,v) ∈ attrs → ∀ c, c ∈ k.data → is_lowercase_letter c) :
  let html_parts := tags.zip attrs_list |>.map (fun (tag, attrs) =>
    let attr_str := String.join (attrs.map (fun (k,v) => s!"{k}=\"{v}\""))
    s!"<{tag} {attr_str}>"
  )
  let html := String.intercalate "\n" html_parts
  let result := split_lines (parse_html html)
  ∀ i : Nat, i < tags.length →
    result[i]! = tags[i]! ∧
    ∀ j k v, attrs_list[i]![j]! = (k,v) →
      result[i + j + 1]! = s!"-> {k} > {v}" :=
sorry

theorem self_closing_tag_parse {tag : String}
  (h : ∀ c, c ∈ tag.data → is_lowercase_letter c) :
  parse_html s!"<{tag}/>" = tag :=
sorry
-- </vc-theorems>