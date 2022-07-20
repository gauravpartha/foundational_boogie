procedure if_example_test_2() {
    var x: int;
    
    havoc x; // ---> [Havoc x] --- block 0

//-------------------------------------------------------

    if (x > 5)
    {
        x := 10; // ---> [Assume x > 5; x := 10] --- block 3
    }
    else
    {
        x := 1; // ---> [Assume 5 >= x; x := 1] --- block 1
    }

//#######################################################

    assert x > 0; // ---> [Assert x > 0] --- block 2
}
