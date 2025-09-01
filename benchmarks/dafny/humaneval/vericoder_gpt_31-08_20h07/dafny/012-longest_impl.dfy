datatype Option<T> = None | Some(T)
function getVal(mx : Option<string>) : string
    requires mx != None
{
    match mx {
        case Some(n) => n
    }
}

// <vc-helpers>

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
    result := None;
  } else {
    var best := strings[0];
    var k := 1;
    while k < |strings|
      invariant 1 <= k <= |strings|
      invariant best in strings
      invariant forall j :: 0 <= j < k ==> |best| >= |strings[j]|
    {
      if |strings[k]| > |best| {
        best := strings[k];
      } else {
        assert |best| >= |strings[k]|;
      }
      k := k + 1;
    }
    result := Some(best);
    assert result != None;
    assert getVal(result) == best;
    assert getVal(result) in strings;

    assert k == |strings|;
    assert forall s :: s in strings ==> |getVal(result)| >= |s|
      by {
        forall s | s in strings
          ensures |getVal(result)| >= |s|
        {
          var i :| 0 <= i < |strings| && strings[i] == s;
          assert |best| >= |strings[i]|;
          assert |getVal(result)| >= |s|;
        }
      }
  }
}
// </vc-code>

