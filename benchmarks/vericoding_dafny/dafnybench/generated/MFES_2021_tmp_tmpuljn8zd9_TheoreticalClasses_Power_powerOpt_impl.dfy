function power(x: real, n: nat) : real
  decreases n
{
    if n == 0 then 1.0 else x * power(x, n-1)
}

// Iterative version, imperative, with time complexity O(n) and space complexity O(1).

// Recursive version, imperative, with time and space complexity O(log n).

// <vc-helpers>
lemma powerSquare(x: real, n: nat)
  ensures power(x, 2*n) == power(x*x, n)
{
  if n == 0 {
    calc == {
      power(x, 2*n);
      power(x, 0);
      power(x*x, 0);
      power(x*x, n);
    }
  } else {
    powerSquare(x, n-1);
    distributiveProperty(x, n, n);
    calc == {
      power(x, 2*n);
      power(x, n + n);
      power(x, n) * power(x, n);
      (x * power(x, n-1)) * (x * power(x, n-1));
      x * x * power(x, n-1) * power(x, n-1);
      (x * x) * (power(x, n-1) * power(x, n-1));
      (x * x) * power(x, 2*(n-1));
      (x * x) * power(x*x, n-1);
      power(x*x, n);
    }
  }
}
// </vc-helpers>

method powerOpt(x: real, n: nat) returns (p : real)
  ensures p == power(x, n);
  decreases n;
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    p := 1.0;
  } else if n % 2 == 0 {
    powerSquare(x, n / 2);
    var temp := powerOpt(x * x, n / 2);
    p := temp;
  } else {
    powerSquare(x, (n - 1) / 2);
    var temp := powerOpt(x * x, (n - 1) / 2);
    p := x * temp;
  }
}
// </vc-code>

// States the property x^a * x^b = x^(a+b), that powerOpt takes advantage of. 
// The annotation {:induction a} guides Dafny to prove the property
// by automatic induction on 'a'.
lemma distributiveProperty(x: real, a: nat, b: nat) 
  ensures power(x, a) * power(x, b)  == power(x, a + b) 
{
  //    
  // To use the proof below, deactivate automatic induction, with {:induction false}.
 if a == 0 {
        // base case
        calc == {
            power(x, a) * power(x, b);
            power(x, 0) * power(x, b); // substitution
            power(x, b); // neutral element of "*"
            power(x, a + b); // neutral element of "+"
        }
    }
    else {
        // recursive case, assuming property holds for a-1 (proof by induction)
        distributiveProperty(x, a-1, b); 
        // now do the proof
        calc == {
            power(x, a) * power(x, b);
            (x * power(x, a-1)) * power(x, b); // by the definition of power
            x * (power(x, a-1) * power(x, b)); // associative property
            x * power(x, a + b - 1); // this same property for a-1
            power(x, a + b); // definition of power
        }
    }
}

// A simple test case to make sure the specification is adequate.