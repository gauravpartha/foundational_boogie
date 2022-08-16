procedure if_example_no_else_branch() {
    var x: int;
    
    havoc x; 

    if (x > 5)
    {
        x := 10; 
    }

    if (x <= 5)
    {
        x := 1;
    }

    assert x > 0; 
}
