Motivation
---------

When compressing sequences of symbols, it is useful to have many equal symbols follow each other, because then they can be encoded with a run length encoding. For example, RLE encoding of `"aaaabbbbbbbbbbbcccccc"` would give something like `4a 11b 6c`.

(Look [here](http://www.codewars.com/kata/run-length-encoding/) for learning more about the run-length-encoding.)

Of course, RLE is interesting only if the string contains many identical consecutive characters. But what bout human readable text? Here comes the Burrows-Wheeler-Transformation.

Transformation
-------------
There even exists a transformation, which brings equal symbols closer together, it is called the **Burrows-Wheeler-Transformation**. The forward transformation works as follows: Let's say we have a sequence with length n, first write every shift of that string into a *n x n* matrix:
```
Input: "bananabar"

b a n a n a b a r
r b a n a n a b a
a r b a n a n a b
b a r b a n a n a
a b a r b a n a n
n a b a r b a n a
a n a b a r b a n
n a n a b a r b a
a n a n a b a r b
```
Then we sort that matrix by its rows. The output of the transformation then is the **last column** and the **row index** in which the original string is in:
```
               .-.
a b a r b a n a n
a n a b a r b a n
a n a n a b a r b
a r b a n a n a b
b a n a n a b a r <- 4
b a r b a n a n a
n a b a r b a n a
n a n a b a r b a
r b a n a n a b a
               '-'

Output: ("nnbbraaaa", 4)
```

```if:java
To handle the two kinds of output data, we will use the preloaded class `BWT`, whose contract is the following:

    public class BWT {

        public String s;
        public int n;

        public BWT(String s, int n)

        @Override public String  toString()
        @Override public boolean equals(Object o)
        @Override public int     hashCode()
    }

```

Of course we want to restore the original input, therefore you get the following hints:

1. The output contains the last matrix column.
2. The first column can be acquired by sorting the last column.
3. **For every row of the table:** Symbols in the first column follow on symbols in the last column, in the same way they do in the input string.
4. You don't need to reconstruct the whole table to get the input back.

Goal
----

The goal of this Kata is to write both, the `encode` and `decode` functions. Together they should work as the identity function on lists. (*Note:* For the empty input, the row number is ignored.)

Further studies
--------------
You may have noticed that symbols are not always consecutive, but just in proximity, after the transformation. If you're interested in how to deal with that, you should have a look at [this Kata](http://www.codewars.com/kata/move-to-front-encoding/).

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded