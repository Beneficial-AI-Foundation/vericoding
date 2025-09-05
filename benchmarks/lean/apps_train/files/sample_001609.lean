Finally the clowns of Synapse have decided to take their site online. The convener of the clowns has heard from somewhere that knowing URI's is very important for their website, so kindly help him with this task.

Uniform Resource Identifiers (or URIs) are strings like
http://synapse.daiict.ac.in/codemutants/, mailto:clown_convener@synapse.daiict.ac.in,
ftp://10.100.93.93/night_halters, or even just output.txt that are
used to identify a resource, usually on the Internet or a local computer.
Certain characters are reserved within URIs, and if a reserved character is
part of an identifier then it must be percent-encoded by
replacing it with a percent sign followed by two hexadecimal digits
representing the ASCII code of the character. A table of seven reserved
characters and their encodings is shown below. Your job is to write a
program that can percent-encode a string of characters.CharacterEncoding" " (space)%20"!" (exclamation point)%21"$" (dollar sign)%24"%" (percent sign)%25"(" (left parenthesis)%28")" (right parenthesis)%29"*" (asterisk)%2a
Input: The input consists of one or more strings, each
1–79 characters long and on a line by itself, followed by a line
containing only "#" that signals the end of the input. The character "#" is
used only as an end-of-input marker and will not appear anywhere else in the
input. A string may contain spaces, but not at the beginning or end of the
string, and there will never be two or more consecutive spaces.
Output: For each input string, replace every occurrence of a
reserved character in the table above by its percent-encoding, exactly as
shown, and output the resulting string on a line by itself. Note that the
percent-encoding for an asterisk is %2a (with a lowercase "a") rather than
%2A (with an uppercase "A").

-----Example-----
Input:
Happy Joy Joy!
http://synapse.daiict.ac.in/
plain_vanilla
(**)
?
the 7% solution
#

Output:
Happy%20Joy%20Joy%21
http://synapse.daiict.ac.in/
plain_vanilla
%28%2a%2a%29
?
the%207%25%20solution

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
