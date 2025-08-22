// RUN: %dafny /compile:0 /rprint:"%t.rprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Tests that come down to comparing the bodies of (possibly nested) functions.
// Many of these currently require far more effort than one would like.
// KRML, 2 May 2016

//ATOM 
// RUN: %dafny /compile:0 /rprint:"%t.rprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Tests that come down to comparing the bodies of (possibly nested) functions.
// Many of these currently require far more effort than one would like.
// KRML, 2 May 2016

function Sum(n: nat, f: int -> int): int
{
  if n == 0 then 0 else f(n-1) + Sum(n-1, f)
}

//ATOM 
lemma Exchange(n: nat, f: int -> int, g: int -> int)
  requires forall i :: 0 <= i < n ==> f(i) == g(i)
  ensures Sum(n, f) == Sum(n, g)
{
}

//ATOM 
lemma ExchangeEta(n: nat, f: int -> int, g: int -> int)
  requires forall i :: 0 <= i < n ==> f(i) == g(i)
  ensures Sum(n, x => f(x)) == Sum(n, x => g(x))
{
}

//ATOM 
lemma NestedAlphaRenaming(n: nat, g: (int,int) -> int)
  ensures Sum(n, x => Sum(n, y => g(x,y))) == Sum(n, a => Sum(n, b => g(a,b)))
{
}

//ATOM 
lemma DistributePlus1(n: nat, f: int -> int)
  ensures Sum(n, x => 1 + f(x)) == n + Sum(n, f)
{
}

//ATOM 
lemma Distribute(n: nat, f: int -> int, g: int -> int)
  ensures Sum(n, x => f(x) + g(x)) == Sum(n, f) + Sum(n, g)
{
}

//IMPL PrettyBasicBetaReduction
lemma PrettyBasicBetaReduction(n: nat, g: (int,int) -> int, i: int)
  ensures (x => Sum(n, y => g(x,y)))(i) == Sum(n, y => g(i,y))
{
  // NOTE: This proof is by induction on n (it can be done automatically)
  if n == 0 {
    calc {
      (x => Sum(n, y => g(x,y)))(i);
      0;
      Sum(n, y => g(i,y));
    }
  } else {
    calc {
      (x => Sum(n, y => g(x,y)))(i);
      g(i,n-1) + (x => Sum(n-1, y => g(x,y)))(i);
      { PrettyBasicBetaReduction(n-1, g, i); }
      g(i,n-1) + Sum(n-1, y => g(i,y));
      (y => g(i,y))(n-1) + Sum(n-1, y => g(i,y));
      Sum(n, y => g(i,y));
    }
  }
}

//ATOM 
lemma BetaReduction0(n: nat, g: (int,int) -> int, i: int)
  ensures (x => Sum(n, y => g(x,y)))(i) == Sum(n, y => g(i,y))
{
  // automatic proof by induction on n
}

//ATOM 
lemma BetaReduction1(n': nat, g: (int,int) -> int, i: int)
  ensures g(i,n') + Sum(n', y => g(i,y)) == (x => g(x,n') + Sum(n', y => g(x,y)))(i);
{
}

//ATOM 
lemma BetaReductionInside(n': nat, g: (int,int) -> int)
  ensures Sum(n', x => g(x,n') + Sum(n', y => g(x,y)))
       == Sum(n', x => (w => g(w,n'))(x) + (w => Sum(n', y => g(w,y)))(x))
{
  forall i | 0 <= i < n'
  {
    calc {
      (x => g(x,n') + Sum(n', y => g(x,y)))(i);
      (x => (w => g(w,n'))(x) + (w => Sum(n', y => g(w,y)))(x))(i);
    }
  }
  Exchange(n', x => g(x,n') + Sum(n', y => g(x,y)), x => (w => g(w,n'))(x) + (w => Sum(n', y => g(w,y)))(x));
}

//ATOM 
lemma L(n: nat, n': nat, g: (int, int) -> int)
  requires && n == n' + 1
  ensures Sum(n, x => Sum(n, y => g(x,y)))
       == Sum(n', x => Sum(n', y => g(x,y))) + Sum(n', x => g(x,n')) + Sum(n', y => g(n',y)) + g(n',n')
{
  var A := w => g(w,n');
  var B := w => Sum(n', y => g(w,y));

  calc {
    Sum(n, x => Sum(n, y => g(x,y)));
    { assume false;/*TODO*/ }
    (x => Sum(n, y => g(x,y)))(n') + Sum(n', x => Sum(n, y => g(x,y)));
    { BetaReduction0(n, g, n'); }
    Sum(n, y => g(n',y)) + Sum(n', x => Sum(n, y => g(x,y)));
    { assume false;/*TODO*/ }
    (y => g(n',y))(n') + Sum(n', y => g(n',y)) + Sum(n', x => Sum(n, y => g(x,y)));
    { assert (y => g(n',y))(n') == g(n',n'); }
    g(n',n') + Sum(n', y => g(n',y)) + Sum(n', x => Sum(n, y => g(x,y)));
    {
      forall i | 0 <= i < n' {
        calc {
          (x => Sum(n, y => g(x,y)))(i);
          { PrettyBasicBetaReduction(n, g, i); }
          Sum(n, y => g(i,y));
          { assume false;/*TODO*/ }
          (y => g(i,y))(n') + Sum(n', y => g(i,y));
          // beta reduction
          g(i,n') + Sum(n', y => g(i,y));
          { BetaReduction1(n', g, i); }
          (x => g(x,n') + Sum(n', y => g(x,y)))(i);
        }
      }
      Exchange(n', x => Sum(n, y => g(x,y)), x => g(x,n') + Sum(n', y => g(x,y)));
    }
    g(n',n') + Sum(n', y => g(n',y)) + Sum(n', x => g(x,n') + Sum(n', y => g(x,y)));
    { BetaReductionInside(n', g); }
    g(n',n') + Sum(n', y => g(n',y)) + Sum(n', x => (w => g(w,n'))(x) + (w => Sum(n', y => g(w,y)))(x));
    { Exchange(n', x => (w => g(w,n'))(x) + (w => Sum(n', y => g(w,y)))(x), x => A(x) + B(x)); }
    g(n',n') + Sum(n', y => g(n',y)) + Sum(n', x => A(x) + B(x));
    { Distribute(n', A, B); }
    g(n',n') + Sum(n', y => g(n',y)) + Sum(n', A) + Sum(n', B);
    // defs. A and B
    g(n',n') + Sum(n', y => g(n',y)) + Sum(n', w => g(w,n')) + Sum(n', w => Sum(n', y => g(w,y)));
    // alpha renamings, and commutativity of the 4 plus terms
    Sum(n', x => Sum(n', y => g(x,y))) + Sum(n', y => g(n',y)) + Sum(n', x => g(x,n')) + g(n',n');
  }
}

//ATOM 
lemma Commute(n: nat, g: (int,int) -> int)
  ensures Sum(n, x => Sum(n, y => g(x,y))) == Sum(n, x => Sum(n, y => g(y,x)))
{
}

//IMPL CommuteSum
lemma CommuteSum(n: nat, g: (int,int) -> int)
  ensures Sum(n, x => Sum(n, y => g(x,y))) == Sum(n, y => Sum(n, x => g(x,y)))
{
  /* code modified by LLM (iteration 1): Use induction with proper application of L lemma and Commute atom */
  if n == 0 {
    calc {
      Sum(n, x => Sum(n, y => g(x,y)));
      0;
      Sum(n, y => Sum(n, x => g(x,y)));
    }
  } else {
    calc {
      Sum(n, x => Sum(n, y => g(x,y)));
      { L(n, n-1, g); }
      Sum(n-1, x => Sum(n-1, y => g(x,y))) + Sum(n-1, x => g(x,n-1)) + Sum(n-1, y => g(n-1,y)) + g(n-1,n-1);
      { CommuteSum(n-1, g); }
      Sum(n-1, y => Sum(n-1, x => g(x,y))) + Sum(n-1, x => g(x,n-1)) + Sum(n-1, y => g(n-1,y)) + g(n-1,n-1);
      /* code modified by LLM (iteration 1): Apply L lemma in reverse with swapped function to get target form */
      { 
        var gSwapped := (y:int, x:int) => g(x,y);
        L(n, n-1, gSwapped);
      }
      Sum(n, y => Sum(n, x => g(x,y)));
    }
  }
}