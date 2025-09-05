`This kata is the first of the ADFGX Ciphers, the harder version can be found `here.

The ADFGX Cipher is a pretty well-known Cryptographic tool, and is essentially a modified Polybius Square.

Rather than having numbers as coordinates on the table, it has the letters:

 `A, D, F, G, X`

Also, because this is the first step, and to help simplify things, you won't have to worry about a key, or the corresponding columnar transposition. In this kata ;)

All you have to do is encrypt and decrypt a string into `ADFGX` format.

`adfgx_encrypt() and adfgx_decrypt()` will be passed a string, `plaintext` and `ciphertext` respectively, and an adfgx`square`, for which will guide the operations. 

Now for some examples to clear confusion:

```python
adfgx_encrypt("helloworld", "bchigklnmoqprstuvwxyzadef")

    A D F G X

A   b c h i g
D   k l n m o     
F   q p r s t  -> square (PLEASE NOTE, j SHOULD BE TREATED AS i)  
G   u v w x y  
X   z a d e f

"helloworld"   -> plaintext

EVALUATES TO:

      F  
          -> "AF"
A     h
--------------
          G 
               -> "XG"  
X         e 

AND SO FORTH...

#Results in:

adfgx_encrypt("helloworld", "bchigklnmoqprstuvwxyzadef") 
==
"AFXGDDDDDXGFDXFFDDXF"
```
Now decryption:
```python
adfgx_decrypt("FGXGADGDXGFXAXXGFGFGAADGXG", "aczlmuqngoipvstkrwfxhdbey) 

    A D F G X

A   a c z l m
D   u q n g o     
F   i p v s t  -> square (PLEASE NOTE, j SHOULD BE TREATED AS i)  
G   k r w f x  
X   h d b e y

"FGXGADGDXGFXAXXGFGFGAADGXG"   -> ciphertext

"FG" == "s"
"XG" == "e"

AND SO ON:

adfgx_decrypt("FGXGADGDXGFXAXXGFGFGAADGXG", "aczlmuqngoipvstkrwfxhdbey) 
==
"secretmessage"
```
PLEASE NOTE: ALL INPUT WILL BE VALID, NO NEED TO ERROR CHECK :D

What are you waiting for?!
Go create `adfgx_encrypt() and adfgx_decrypt()`!

Good Luck!

def adfgx_encrypt (plaintext : String) (square : String) : String :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded