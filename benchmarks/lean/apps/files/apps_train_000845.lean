/-
The entire network is under the inspection and direct control of the Decepticons. They have learned our language through the World Wide Web and can easily understand the messages which are being sent. Sam is trying to send the information to Autobots to locate “ALL SPARK” which is the only source of energy that can be used to create universe. He is bit cautious in sending the message. He is sending the messages in a form of special pattern of string that contains important message in form of substrings. But Decepticons have learnt to recognize the Data Mining and string comparison patterns. He is sending a big message in form of a string (say M) and let there are N smaller substrings. Decepticons have to find whether each of these N substrings is a sub-string of M. All strings consist of only alphanumeric characters.

-----Input-----
Input to the program consists of two line. The first line contains the string M (where size of M should be <=40). The next line contain a string S.

-----Output-----
Output should consist of a line with a character 'Y'/'N' indicating whether the string S is a sub-string of String M or not.

-----Example-----
Input:
techtrishna online event
onlin
Output:
Y
-/

-- <vc-helpers>
-- </vc-helpers>

def is_substring (main_str : String) (sub_str : String) : String := sorry

theorem is_substring_returns_y_or_n (main_str sub_str : String) :
  (is_substring main_str sub_str = "Y") ∨ (is_substring main_str sub_str = "N") := sorry

theorem empty_string_is_substring (main_str : String) :
  is_substring main_str "" = "Y" := sorry

theorem string_is_substring_of_itself (str : String) :
  is_substring str str = "Y" := sorry 

theorem substring_result_matches_existence (main_str sub_str : String) :
  (is_substring main_str sub_str = "Y" ↔ ∃ a b : String, a ++ sub_str ++ b = main_str) := sorry

theorem substring_of_concatenation_left (s1 s2 : String) :
  is_substring (s1 ++ s2) s1 = "Y" := sorry

theorem substring_of_concatenation_right (s1 s2 : String) :
  is_substring (s1 ++ s2) s2 = "Y" := sorry

/-
info: 'Y'
-/
-- #guard_msgs in
-- #eval is_substring "techtrishna online event" "onlin"

/-
info: 'N'
-/
-- #guard_msgs in
-- #eval is_substring "hello world" "xyz"

/-
info: 'Y'
-/
-- #guard_msgs in
-- #eval is_substring "python3" "thon"

-- Apps difficulty: interview
-- Assurance level: unguarded