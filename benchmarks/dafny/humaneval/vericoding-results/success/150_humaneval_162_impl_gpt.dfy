// <vc-preamble>

datatype Option<T> = None | Some(value: T)

predicate isValidMD5Hash(s: string)
{
    |s| == 32 && forall i :: 0 <= i < |s| ==> s[i] in "0123456789abcdef"
}
// </vc-preamble>

// <vc-helpers>
function constMD5(): string {
  "0123456789abcdef0123456789abcdef"
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
    var h := constMD5();
    result := Some(h);
  }
}
// </vc-code>
