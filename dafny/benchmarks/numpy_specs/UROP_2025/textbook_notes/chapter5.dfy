//CHAPTER FIVE: LEMMAS AND PROOFS

/*
5.0: Declaring a Lemma
lemma >> mathematical assertion that has a proof
not compiled into code at runtime: used only by the verifier
*/

function More(x: int): int {
    if x <=0 then 1 else More(x-2) +3
}

lemma Increasing(x: int)
    ensures x < More(x)

method ExampleLemmaUse(a: int){
    var b:= More (a);
    var c:= More(b);
   // assert 2 <= c-a; //cant verify because it doesnt know enough about More
}

method ExampleLemmaUse'(a: int){
    var b:= More (a);
    Increasing(a);
    Increasing(b);
    var c:= More(b);
    assert 2 <= c-a; //cant verify because it doesnt know enough about More
}

/*
5.2 Proving a Lemma
the one above is automatically proved by Dafny using induction
*/

lemma {:induction false} Increasing' (x:int)
    ensures x < More(x) //breaks because induction is turned off 
{
}

lemma {:induction false} Increasing'' (x:int)
    ensures x < More(x) //breaks because induction is turned off 
{
    if x <= 0 {}
    else{
        Increasing(x-2);
    }
}

/*
5.3 Back to Basics 
how does this proof work using hoare logic
*/

lemma {:induction false} Increasing'''(x:int)
    ensures x < More(x) //breaks because induction is turned off 
{
    if x <= 0 {
        // assert x <= 0;
        // assert x <= 0 && More(x) == 1; 
        // assert x < More(x);
        assert More(x) == 1; // More when x < 0
    }
    else{
        assert 0 < x;
        assert 0 < x && More(x) == More(x-2) +3;
        Increasing(x-2);
        assert 0 < x && More(x) == More(x-2) +3 && x-2 < More(x-2);
        assert More(x) == More(x-2) + 3 && x+1 < More(x-2) + 3;
        assert x+1 < More(x);
        assert x < More(x);
    }
}

/*
5.4 Proof Calculations
list of expressions linked witha  chain of operators 
 */
//example
lemma docalc(x : int, y: int)
  ensures (x + y) * (x + y) == x * x + 2 * x * y + y * y
{
  calc {
    (x + y) * (x + y);
    ==
    // distributive law: (a + b) * c == a * c + b * c
    x * (x + y) + y * (x + y);
    ==
    // distributive law: a * (b + c) == a * b + a * c
    x * x + x * y + y * x + y * y;
    ==
    calc {
	    y * x;
      ==
	    x * y;
    }
    x * x + x * y + x * y + y * y;
    ==
    calc {
      x * y + x * y;
      ==
      // a = 1 * a
      1 * x * y + 1 * x * y;
      ==
      // Distributive law
      (1 + 1) * x * y;
      ==
      2 * x * y;
    }
    x * x + 2 * x * y + y * y;
    }
}
//skipped a bunch of examples