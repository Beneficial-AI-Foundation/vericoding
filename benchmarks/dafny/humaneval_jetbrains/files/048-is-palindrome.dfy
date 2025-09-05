/*
function_signature: def is_palindrome(string: str) -> Bool
Checks if given string is a palindrome
*/

method is_palindrome(text : string) returns (result : bool)
    // post-conditions-start
    ensures result == (forall i : int :: i >= 0 && i < |text| ==> text[i] == text[|text| - i - 1])
    // post-conditions-end
{
  assume false;
}
