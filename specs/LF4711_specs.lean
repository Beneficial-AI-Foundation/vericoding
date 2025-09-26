-- <vc-preamble>
def HtmlGen.tag (t : HtmlTag) (content : String) : String := sorry

theorem tag_structure {t : HtmlTag} {content : String} :
  let result := HtmlGen.tag t content
  result.startsWith s!"<{repr t}>" ∧ 
  result.endsWith s!"</{repr t}>" ∧
  result = s!"<{repr t}>{content}</{repr t}>" := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def HtmlGen.comment (content : String) : String := sorry

theorem comment_structure {content : String} :
  let result := HtmlGen.comment content
  result.startsWith "<!--" ∧
  result.endsWith "-->" ∧ 
  result = s!"<!--{content}-->" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem nested_tags {outer inner : HtmlTag} {content : String} :
  let innerResult := HtmlGen.tag inner content
  let result := HtmlGen.tag outer innerResult
  result = s!"<{repr outer}><{repr inner}>{content}</{repr inner}></{repr outer}>" := sorry

theorem custom_tag_direct {content : String} :
  HtmlGen.tag HtmlTag.custom content = s!"<custom>{content}</custom>" := sorry
-- </vc-theorems>