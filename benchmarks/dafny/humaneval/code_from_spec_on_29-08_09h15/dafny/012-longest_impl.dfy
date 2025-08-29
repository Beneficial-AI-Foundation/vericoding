datatype Option<T> = None | Some(T)
function getVal(mx : Option<string>) : string
    requires mx != None
{
    match mx {
        case Some(n) => n
    }
}

// <vc-helpers>
lemma FirstOfMaxLengthExists(strings: seq<string>)
  requires |strings| > 0
  ensures exists i :: 0 <= i < |strings| && (forall j :: 0 <= j < |strings| ==> |strings[i]| >= |strings[j]|)
{
  var maxLen := |strings[0]|;
  var i := 1;
  while i < |strings|
    invariant 1 <= i <= |strings|
    invariant forall j :: 0 <= j < i ==> |strings[j]| <= maxLen
    invariant exists k :: 0 <= k < i && |strings[k]| == maxLen
  {
    if |strings[i]| > maxLen {
      maxLen := |strings[i]|;
    }
    i := i + 1;
  }
  
  i := 0;
  while i < |strings|
    invariant 0 <= i <= |strings|
    invariant forall j :: 0 <= j < |strings| ==> |strings[j]| <= maxLen
    invariant exists k :: 0 <= k < |strings| && |strings[k]| == maxLen
  {
    if |strings[i]| == maxLen {
      assert forall j :: 0 <= j < |strings| ==> |strings[i]| >= |strings[j]|;
      return;
    }
    i := i + 1;
  }
}

lemma MaxLengthStringExists(strings: seq<string>, maxLen: int)
  requires |strings| > 0
  requires forall j :: 0 <= j < |strings| ==> |strings[j]| <= maxLen
  requires exists k :: 0 <= k < |strings| && |strings[k]| == maxLen
  ensures exists i :: 0 <= i < |strings| && |strings[i]| == maxLen
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def longest(strings: List[str]) -> Optional[str]
Out of list of strings, return the longest one. Return the first one in case of multiple strings of the same length. Return None in case the input list is empty.
*/
// </vc-description>

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
    result := None;
  } else {
    FirstOfMaxLengthExists(strings);
    var maxLen := |strings[0]|;
    var i := 1;
    while i < |strings|
      invariant 1 <= i <= |strings|
      invariant forall j :: 0 <= j < i ==> |strings[j]| <= maxLen
      invariant exists k :: 0 <= k < i && |strings[k]| == maxLen
    {
      if |strings[i]| > maxLen {
        maxLen := |strings[i]|;
      }
      i := i + 1;
    }
    
    MaxLengthStringExists(strings, maxLen);
    
    i := 0;
    while i < |strings|
      invariant 0 <= i <= |strings|
      invariant forall j :: 0 <= j < |strings| ==> |strings[j]| <= maxLen
      invariant exists k :: 0 <= k < |strings| && |strings[k]| == maxLen
    {
      if |strings[i]| == maxLen {
        result := Some(strings[i]);
        return;
      }
      i := i + 1;
    }
  }
}
// </vc-code>

