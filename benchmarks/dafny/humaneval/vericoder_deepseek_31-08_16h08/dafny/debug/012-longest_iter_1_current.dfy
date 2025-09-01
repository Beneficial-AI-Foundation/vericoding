datatype Option<T> = None | Some(T)
function getVal(mx : Option<string>) : string
    requires mx != None
{
    match mx {
        case Some(n) => n
    }
}

// <vc-helpers>
lemma MaxLemma(s: seq<string>, max: string)
  requires |s| > 0
  requires max in s
  requires forall x :: x in s ==> |max| >= |x|
  ensures exists m :: m in s && forall x :: x in s ==> |m| >= |x|
{
}

lemma MaxExists(s: seq<string>)
  requires |s| > 0
  ensures exists m :: m in s && forall x :: x in s ==> |m| >= |x|
{
  var i := 0;
  var max := s[0];
  
  while i < |s|
    invariant 0 <= i <= |s|
    invariant max in s[0..i]
    invariant forall x :: x in s[0..i] ==> |max| >= |x|
  {
    if |s[i]| > |max| {
      max := s[i];
    }
    i := i + 1;
  }
  
  MaxLemma(s, max);
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
    result := None;
  } else {
    var i := 0;
    var max := strings[0];
    
    while i < |strings|
      invariant 0 <= i <= |strings|
      invariant max in strings[0..i]
      invariant forall x :: x in strings[0..i] ==> |max| >= |x|
    {
      if |strings[i]| > |max| {
        max := strings[i];
      }
      i := i + 1;
    }
    
    result := Some(max);
  }
}
// </vc-code>

