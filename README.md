# byters

a collection of utilities i find myself implementing everytime i work with bits and bytes in rust collected into a single crate.
this crate treats bits as 0 indexed, starting at the least significant bit.

these utilities include:

- reading single or multiple bits from a primitiv number type
- reading bytes as a primitiv number type with a specifc byte ordering
- converting primitive number types into a slice of bytes with a specific byte ordering
- setting or unsetting bits

