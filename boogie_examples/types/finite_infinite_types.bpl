type A B;

const unique a1: A int;
const unique a2: A int;
const unique a3: A int;

procedure m() returns () {

    //this should go through
    assert a1 != a2 &&  a1 != a3 && a2 != a3;

    assume (forall a:A int :: a == a1 || a == a2 || a == a3);

    //I think this should not got through in general: types can be finite
    //the finite keyword is deprecated
    assert false; 
}