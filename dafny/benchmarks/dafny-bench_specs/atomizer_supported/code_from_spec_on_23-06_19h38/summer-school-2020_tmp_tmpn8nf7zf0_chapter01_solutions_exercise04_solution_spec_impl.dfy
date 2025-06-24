// Predicates

// A common thing you'll want is a function with a boolean result.
// ATOM 
// Predicates

// A common thing you'll want is a function with a boolean result.
function AtLeastTwiceAsBigFunction(a:int, b:int) : bool
{
  a >= 2*b
}


// It's so fantastically common that there's a shorthand for it: `predicate`.
// ATOM 

// It's so fantastically common that there's a shorthand for it: `predicate`.
predicate AtLeastTwiceAsBigPredicate(a:int, b:int)
{
  a >= 2*b
}


// ATOM 

function Double(a:int) : int
{
  2 * a
}


// ATOM 

lemma TheseTwoPredicatesAreEquivalent(x:int, y:int)
{
}


// Add a precondition to make this lemma verify.
// ATOM 

// Add a precondition to make this lemma verify.
lemma FourTimesIsPrettyBig(x:int)
  requires x>=0
{
}