contract SymVars {
    
    function addTo(uint number) returns (uint) {
        var a = 1;
        var c = inc(a);
        var b = c + number;
        
        return b;
        
    }


    function inc(uint k) returns (uint) {

        return (k + 100);

    }

}

