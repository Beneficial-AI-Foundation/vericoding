[BasE91](http://base91.sourceforge.net/) is a method for encoding binary as ASCII characters. It is more efficient than Base64 and needs 91 characters to represent the encoded data.

The following ASCII charakters are used:

    'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789'
    '!#$%&()*+,./:;<=>?@[]^_`{|}~"'

Create two functions that encode strings to basE91 string and decodes the other way round. 

    b91encode('test') = 'fPNKd'
    b91decode('fPNKd') = 'test'

    b91decode('>OwJh>Io0Tv!8PE') = 'Hello World!'
    b91encode('Hello World!') = '>OwJh>Io0Tv!8PE'

Input strings are valid.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded