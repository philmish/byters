# byters

as i find myself re-implementing the same utilities every time i build something which works with or parses bytes i summarized these utilities in this crate.
most of the code consists of simple bit-shiftig operations or thin wrappers around functionality the rust standard library provides, pulled together for ease of use.

these utilities include:
    - reading single or multiple bits from a primitiv number type
    - reading bytes as a primitiv number type with a specifc byte ordering
    - converting primitive number types into a slice of bytes with a specific byte ordering
    - setting or unsetting bits
    
