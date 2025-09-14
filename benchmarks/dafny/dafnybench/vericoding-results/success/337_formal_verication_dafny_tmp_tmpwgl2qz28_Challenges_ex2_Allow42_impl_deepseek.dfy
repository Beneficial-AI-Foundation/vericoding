/*
    i)  Write a verified method with signature

// <vc-helpers>
predicate SafeDivision(x: int, d: int) {
  d != 0
}

lemma DivisionLemma(x: int, d: int)
  requires d != 0
  ensures x / d == x / d
{
}
// </vc-helpers>

// <vc-spec>
method Allow42(x:int, y:int) returns (z: int, err:bool) 
ensures y != 42 ==> z == x/(42-y) && err == false;
ensures y == 42 ==> z == 0 && err == true;
// </vc-spec>
// <vc-code>
if y == 42 {
  z := 0;
  err := true;
} else {
  var d := 42 - y;
  assert SafeDivision(x, d) by {
    assert d != 0;
  }
  DivisionLemma(x, d);
  z := x / d;
  err := false;
}
// </vc-code>

