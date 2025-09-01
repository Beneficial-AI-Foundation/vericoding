datatype Option<T> = None | Some(T)
function getVal(mx : Option<string>) : string
    requires mx != None
{
    match mx {
        case Some(n) => n
    }
}

// <vc-helpers>
function method in_seq<T>(s: T, seq: seq<T>): bool
  reads seq
{
  exists i :: 0 <= i < |seq| && seq[i] == s
}
// </vc-helpers>

// <vc-spec>
method longest(strings: seq<string>) returns (result : Option<string>)
  // post-conditions-start
  ensures result == None <==> |strings| == 0
  ensures result != None ==> forall s :: s in strings ==> |getVal(result)| >= |s|
  ensures result != None ==> getVal(result) in strings 
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if |strings| == 0 {
    return None;
  } else {
    var longest_so_far := strings[0];
    var i := 1;
    while i < |strings|
      invariant 0 < |strings|
      invariant 0 < i <= |strings|
      invariant in_seq(longest_so_far, strings)
      invariant forall k :: 0 <= k < i ==> |longest_so_far| >= |strings[k]|
    {
      if |strings[i]| > |longest_so_far| {
        longest_so_far := strings[i];
      }
      i := i + 1;
    }
    return Some(longest_so_far);
  }
}
// </vc-code>

