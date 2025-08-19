//ATOM

predicate IsDigit(c: char)
{
  48 <= c as int <= 57
}


// SPEC

method IsInteger(s: string) returns (result: bool)
  ensures result <==> (|s| > 0) && (forall i :: 0 <= i < |s| ==> IsDigit(s[i]))
{
}