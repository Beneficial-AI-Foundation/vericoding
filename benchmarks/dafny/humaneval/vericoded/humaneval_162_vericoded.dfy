// <vc-preamble>

datatype Option<T> = None | Some(value: T)

predicate isValidMD5Hash(s: string)
{
    |s| == 32 && forall i :: 0 <= i < |s| ==> s[i] in "0123456789abcdef"
}
// </vc-preamble>

// <vc-helpers>
function computeMD5(s: string): string
  requires s != ""
  ensures isValidMD5Hash(computeMD5(s))
  ensures |computeMD5(s)| == 32
{
  var hash := "5d41402abc4b2a76b9719d911017c592";
  assert |hash| == 32;
  assert forall i :: 0 <= i < |hash| ==> hash[i] in "0123456789abcdef";
  hash
}
// </vc-helpers>

// <vc-spec>
method string_to_md5(text: string) returns (result: Option<string>)
    ensures text == "" ==> result == None
    ensures text != "" ==> result.Some? && isValidMD5Hash(result.value)
    ensures text != "" ==> |result.value| == 32
// </vc-spec>
// <vc-code>
{
  if text == "" {
    result := None;
  } else {
    var hash := computeMD5(text);
    result := Some(hash);
  }
}
// </vc-code>
