# Task
 You are implementing your own HTML editor. To make it more comfortable for developers you would like to add an auto-completion feature to it.

 Given the starting HTML tag, find the appropriate end tag which your editor should propose.

# Example

 For startTag = "<button type='button' disabled>", the output should be "</button>";

 For startTag = "<i>", the output should be "</i>".

# Input/Output

 - `[input]` string `startTag`/`start_tag`

 - `[output]` a string

def html_end_tag_by_start_tag (start_tag: String) : String :=
  sorry

def is_valid_tag_char (c: Char) : Bool :=
  sorry

def is_valid_tag_first_char (c: Char) : Bool :=
  sorry

def is_valid_attr_name_char (c: Char) : Bool :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded