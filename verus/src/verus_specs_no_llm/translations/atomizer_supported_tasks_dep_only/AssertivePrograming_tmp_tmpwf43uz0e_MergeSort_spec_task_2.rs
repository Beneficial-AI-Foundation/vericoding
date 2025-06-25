// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Sorted(q: Seq<int>) -> bool {
    forall i,j :: 0 <= i <= j < q.len() ==> q.spec_index(i) <= q.spec_index(j)
}

fn Merge(b: Vec<int>, c: Vec<int>, d: Vec<int>, correctly, efficiently, clearly

DO NOT modify the specification or any other part of the method's signature
*/
// SPEC 
method Merge(b: Vec<int>, c: Vec<int>, d: Vec<int>, c: Vec<int>, d: Vec<int>, i0: nat, j0: nat) -> (i: nat, j: nat)
		requires b != c && b != d && b.Length == c.Length + d.Length
		requires Sorted(c[..]) && Sorted(d[..])
		requires i0 <= c.Length && j0 <= d.Length && i0 + j0 <= b.Length
		requires InvSubSet(b[..], c[..], d[..], i0, j0)
		requires InvSorted(b[..], c[..], d[..], i0, j0)
		requires i0 + j0 < b.Length

		modifies b

		ensures i <= c.Length && j <= d.Length && i + j <= b.Length
		ensures InvSubSet(b[..], c[..], d[..], i, j)
		ensures InvSorted(b[..], c[..], d[..], i, j)
		//decreases ensures
		ensures 0 <= c.Length - i < c.Length - i0 || (c.Length - i == c.Length - i0 && 0 <= d.Length - j < d.Length - j0)
		{

			i, j: = i0, j0;
				
				if(i == c.Length || (j< d.Length && d[j] < c[i])){
					// in this case we take the next value from d
				b[i+j]: = d[j];
				lemmaInvSubsetTakeValueFromD(b[..], c[..], d[..], i, j);

				j: = j + 1;
			}
			else{
					// in this case we take the next value from c
				
				b[i+j] := c[i];

				lemmaInvSubsetTakeValueFromC(b[..], c[..], d[..], i, j);
				i: = i + 1;
			}


		}

	
//Loop invariant - b is sprted so far and the next two potential values that will go into b are bigger then the biggest value in b.
//ATOM_PLACEHOLDER_InvSorted


//Loop invariant - the multiset of the prefix of b so far is the same multiset as the prefixes of c and d so far.
//ATOM_PLACEHOLDER_InvSubSet

//This lemma helps dafny see that if the prefixs of arrays are the same multiset until the end of the arrays, //all the arrays are the same multiset.
// ATOM 

//This lemma helps dafny see that if the prefixs of arrays are the same multiset until the end of the arrays, //all the arrays are the same multiset.
lemma LemmaMultysetsEquals (b: Seq<int>, c: Seq<int>, d: Seq<int>, i: nat, j: nat)
    requires
        b != c && b != d && b.len() == c.len() + d.len(),
        Sorted(c.spec_index(..)) && Sorted(d.spec_index(..)),
        b != c && b != d && b.len() == c.len() + d.len(),
        Sorted(c.spec_index(..)) && Sorted(d.spec_index(..)),
        b != c && b != d && b.len() == c.len() + d.len(),
        Sorted(c.spec_index(..)) && Sorted(d.spec_index(..)),
        i0 <= c.len() && j0 <= d.len() && i0 + j0 <= b.len(),
        InvSubSet(b.spec_index(..),c.spec_index(..),d.spec_index(..),i0,j0),
        InvSorted(b.spec_index(..),c.spec_index(..),d.spec_index(..),i0,j0),
        i0 + j0 < b.len()

		modifies b,
        i == c.len(),
        j == d.len(),
        i + j == b.len(),
        multiset(b.spec_index(..i+j)) == multiset(c.spec_index(..i)) + multiset(d.spec_index(..j))
    ensures
        Sorted(b.spec_index(..)) && multiset(b.spec_index(..)) == multiset(c.spec_index(..))+multiset(d.spec_index(..))
	modifies b,
        Sorted(b.spec_index(..)) && multiset(b.spec_index(..)) == multiset(c.spec_index(..))+multiset(d.spec_index(..))
	modifies b,
        i <= c.len() && j <= d.len() && i + j <= b.len(),
        InvSubSet(b.spec_index(..),c.spec_index(..),d.spec_index(..),i,j),
        InvSorted(b.spec_index(..),c.spec_index(..),d.spec_index(..),i,j)
		//decreases,
        ensures 0 <= c.len() - i < c.len() - i0 || (c.len() - i == c.len() - i0 && 0 <= d.len() - j < d.len() - j0),
        multiset(b.spec_index(..)) == multiset(c.spec_index(..))+multiset(d.spec_index(..))
{
    return (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, Seq::empty(), Seq::empty(), Seq::empty(), 0, 0);
}

}