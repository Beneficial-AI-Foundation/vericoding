[The Vigenère cipher](https://en.wikipedia.org/wiki/Vigen%C3%A8re_cipher) is a classic cipher that was thought to be "unbreakable" for three centuries. We now know that this is not so and it can actually be broken pretty easily.

**How the Vigenère cipher works**:

The basic concept is that you have a `message` and a `key`, and each character in the `message` is encrypted using a character in the `key`, by applying a Caesar shift. The key is recycled as many times as needed.

You might want to try [this kata](https://www.codewars.com/kata/vigenere-cipher-helper) first, which focuses on the encryption and decryption processes.

## Well how do we break it?

The first thing we have to do is determine the **length of the key** that was used to encrypt the message.

Write a function that takes some cipher text and a maximum possible key length and returns the length of the key that was used in the encryption process.

**Note:** We don't care about what characters are in the key -- only how many of them there are.

---

Any feedback (and suggestions) would be much appreciated

*This kata is based on one of the programming assignments in [Prof. Jonathan Katz's course on cryptography](https://www.coursera.org/course/cryptography) given on Coursera*

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible