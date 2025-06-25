// SPEC
method foo2() 
  ensures false
{
}

// Specify a post-condition and prove it.

/**
 * Example 2.
 *
 * Find a key in an array.
 *
 * @param   a  The array.
 * @param   key The key to find.
 * @returns    An index i such a[i] == key if key in a and -1 otherwise.
 *
 * Try to:
 * 0. uncomment line index := index + 2 and check problems
 * 1. write the property defined by the @returns above
 * 2. prove this property (you may add loop invariants)
 *
 * @note    The code below is flawed on purpose.
 *       |a| is the length of a
 *       to test whether an integer `k` is in `a`: k in a (true
 *       iff exists 0 <= i < |a|, a[i] == k). 
 *       And: !(k in a) <==> k !in a
 *       a[i..j] is the sub sequence a[i], ..., a[j - 1] 
 *       a[..j] is a[0..j] and a[i..] is a[i..|a|]
 *       a[..] is same as a
 */
