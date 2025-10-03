//Build a circuit with no inputs and one output. 
//That output should always drive 1 

module top_module(output one);

     assign one = 1'b1;   // 1-bit binary constant 1
     or equivalently:
     assign one = 1'b0;   // if you wanted logic 0

endmodule

//build a circuit with no inputs and one output.
//That output should always drive 0
module top_module( output zero);

   assign zero = 0;

end module


//verilog language - the basics

//wire

//create module with one input and one output that behaves like a wire
//module top_module( input in, output out );

//    assign out=in;
    //since wires are directional
    //assign in=out; will be illegal

//endmodule

//4 wires
// 3 inputs, 4 outputs that behaves 
// a-w , b-x, b-y, c-z

module top_module( 
    input a,b,c,
    output w,x,y,z
     );
     assign w=a;
     assign x=b;
     assign y=b;
     assign z=c;

endmodule

//inverter
//not gate

module top_module( input in, output out );

    assign out = ~in;
endmodule

//and gate
module top_module( 
    input a, 
    input b, 
    output out );
 	assign out = a&b;
endmodule

//nor gate
module top_module( 
    input a, 
    input b, 
    output out );
    assign out = ~(a||b);
endmodule


//xnor gate
module top_module(
    input a,
    input b,
    output out);
    assign out = ~(a^b);
endmodule
)

//wire declaration
 
`default_nettype none
module top_module(
    input a,
    input b,
    input c,
    input d,
    output out,
    output out_n   ); 
	wire and1;
    wire and2;
    assign and1= a&b;
    assign and2= c&d;
   
    assign out_n= ~(and1|and2);
    assign out= (and1|and2);
    
endmodule

//7458 chip, 4 and gates and 2 or gates. 10 inputs and 2 outputs

module top_module ( 
    input p1a, p1b, p1c, p1d, p1e, p1f,
    output p1y,
    input p2a, p2b, p2c, p2d,
    output p2y );
	wire and1;
    assign and1 = p1a&p1c&p1b;
    wire and2;
    assign and2=p1f&p1d&p1e;
    wire and3;
    assign and3 = p2a&p2b;
    wire and4;
    assign and4=p2c&p2d;
    assign p2y= (and3 | and4);
    assign p1y = (and1 | and2);
    

endmodule

//VECTORS
// they are used to group related signals using one name
// to make it more convinient to manipulate. 
//its kinda like arrays in C
module top_module ( 
    input wire [2:0] vec,
    output wire [2:0] outv,
    output wire o2,
    output wire o1,
    output wire o0  ); 
    
    //Notice that the declaration of a vector places the dimensions before the name of the vector, which is unusual 
    //compared to C syntax. However, the part select has the dimensions after the vector name as you would expect.
    
    //declaring something "input" or "output" automatically declares it  as a wire
    
    assign outv = vec;
    assign   o0 = vec[0];
    assign   o1 = vec[1];
    assign   o2 = vec[2];
endmodule

//vector1
// declaration types can be
// type [upper:lower] vector name;
//type specifies the datatype of the vector
// this is usually wire or reg

//build a combinational ciruit
//that splits an input half word(16bits, 15:0 into lower [7:0] and upper 
//[15:8] bytes)

`default_nettype none     // Disable implicit nets. Reduces some types of bugs.
module top_module( 
    input wire [15:0] in,
    output wire [7:0] out_hi,
    output wire [7:0] out_lo );
    assign out_hi = in[15:8] ;
    assign out_lo = in[7:0];

endmodule

//vector2
// Build a circuit that will reverse the byte ordering of the 4-byte word.
//A 32-bit vector can be viewed as containing 4 bytes 
//(bits [31:24], [23:16], etc.)

// byte reversal
module top_module( 
    input [31:0] in,
    output [31:0] out );//

    // assign out[31:24] = ...;
    assign out[7:0] = in[31:24];
    assign out[15:8] = in[23:16];
    assign out[23:16]= in[15:8];
    assign out[31:24] = in[7:0];
 
    
    
endmodule

//bitwise operators
// build a circuit that has 2 3-bit inputs 
//that computers the bitwise or of the 
//2 vectors
module top_module( 
    input [2:0] a,
    input [2:0] b,
    output [2:0] out_or_bitwise,
    output out_or_logical,
    output [5:0] out_not
);
	assign out_or_bitwise = a|b;
    assign out_or_logical = a||b;
    assign out_not[2:0] = ~a;
    assign out_not[5:3] = ~b;
endmodule


//four input gates
//build a combinational circuit with four inputs 
// in[3:0]
module top_module( 
    input [3:0] in,
    output out_and,
    output out_or,
    output out_xor
);

     assign out_and = in[3] && in[2] && in[1] && in[0];
    assign out_or = in[3] || in[2] || in[1] || in[0];
    assign out_xor = in[3] ^ in[2] ^ in[1] ^ in[0];
endmodule

//vector 3 
module top_module (
    input [4:0] a, b, c, d, e, f,
    output [7:0] w, x, y, z );//
	//Concatenation needs to know the width of every component (or how would you know the length of the result?). 
    //Thus, {1, 2, 3} is illegal and results in the error message: unsized constants are not allowed in concatenations.
	//The concatenation operator can be used on both the left and right sides of assignments.
    
    wire [31:0] concat_reg; //raise an error when work with reg. Reason unknown???
    assign concat_reg = {a[4:0], b[4:0], c[4:0], d[4:0], e[4:0], f[4:0], 2'b11};
    // why we define 2'b11
    // since a.b.c.d.e.f are 5 bits each
    // that leaves us with 2 bits to define
    //this matches the 32 bits of concat_reg
    //if we dont define these 2 bits
    // we will get x's in the output
    // since they are undefined
    // and verilog will assign x's to undefined bits
    assign w = concat_reg[31:24];
    assign x = concat_reg[23:16];
    assign y = concat_reg[15:8];
    assign z = concat_reg[7:0];

endmodule

//vector reversal 1
//given an 8-bit input vector,
// reverse the its bit in ordering
module top_module( 
    input [7:0] in,
    output [7:0] out
);
    //define every single input to reverse to thru 0 to 7
    assign out[7:0] = { in[0],in[1],in[2],in[3],in[4],in[5],in[6],in[7]};
endmodule

//replication operator
module top_module (
    input [7:0] in,
    output [31:0] out );//
	// The replication operator allows repeating a vector and concatenating them together:
	//{num{vector}}
    
    //this is sign-extending a smaller number to a larger one
    //so when you do 24{in[7]} you are repeating the sign bit 24 times
    // then concatenating it with the original 8 bits

    assign out = { {24{in[7]}} , in[7:0] };

endmodule

//more replication
// give five 1-bit signals (a,b,c,d,e) and compute
//all 25 pairwise one bit comparisons in the 
// 25 one bit comparisons 
module top_module (
    input a, b, c, d, e,
    output [24:0] out );//
    
    // we can use the replication operator to 
    // replicate each input 5 times
    // then concatenate them together
    // then xor the two concatenated vectors
    // to get all pairwise comparisons
      assign out = ~{ {5{a}},{5{b}},{5{c}},{5{d}},{5{e}}} ^ { {5{a,b,c,d,e}}};  
    end module

//modules
//they are circuits that interact with outside through
//input and output ports
module top_module ( input a, input b, output out );
    mod_a instance_1(a,b,out);
endmodule

//connecting posts by position
  module top_module ( 
    input a, 
    input b, 
    input c,
    input d,
    output out1,
    output out2
);
    mod_a instance1(out1,out2,a,b,c,d);
   
    

endmodule

//connecting ports by name
module top_module ( 
    input a, 
    input b, 
    input c,
    input d,
    output out1,
    output out2
);
    //connect ports by name
    mod_a inst_1(.in1(a), .in2(b), .in3(c), .in4(d), .out1(out1), .out2(out2));

endmodule

// 3 modules
// shift is done by module my_dff (input clk, input d,output q):

module top_module(input clk, input d, output q);
    wire con1, con2;
 my_dff d_flop1(.clk(clk),.d(d),.q(con1));
    my_dff d_flop2(.clk(clk),.d(con1),.q(con2));
    my_dff d_flop3(.clk(clk),.d(con2),.q(q));
endmodule

//module & vectors shift8
 module top_module ( 
    input clk, 
    input [7:0] d, 
    input [1:0] sel, 
    output reg [7:0] q 
);
    wire [7:0]con1,con2,con3;
    
    my_dff8 d_flop1(.clk(clk), .d(d), .q(con1));
    my_dff8 d_flop2(.clk(clk), .d(con1), .q(con2) );
    my_dff8 d_flop3(.clk(clk), .d(con2), .q(con3));
    
    always @ (*) begin
        case(sel)
            0 : q = d ;
            1 : q = con1;
            2 : q = con2;
            3 : q = con3;
        endcase
        
        /*if(sel==2'b00)
            q=d;
        else if( sel == 2'b01)
      		q = con1;
        else if( sel == 2'b10)
      		q = con2;
        else if( sel == 2'b11)
      		q = con3;
 		*/
 	end
    
endmodule

//adder1
module top_module(
    input [31:0] a,
    input [31:0] b,
    output [31:0] sum
);
    wire con1, con2;
    add16 adder_1(a[15:0], b[15:0], 0, sum[15:0], con1);
    add16 adder_2(a[31:16], b[31:16], con1, sum[31:16], con2);

endmodule

//adder2
// here you implement adder as well as module
module top_module (
    input [31:0] a,
    input [31:0] b,
    output [31:0] sum
);//
	wire con1, con2;
    add16 adder_1(a[15:0], b[15:0], 0, sum[15:0], con1);
    add16 adder_2(a[31:16], b[31:16], con1, sum[31:16], con2);
endmodule

module add1 ( input a, input b, input cin,   output sum, output cout );
    assign sum  = a^b^cin;
    assign cout = (a&b)|(a&cin)|(b&cin);
endmodule

//carry select adder
module top_module(
    input [31:0] a,
    input [31:0] b,
    output reg [31:0] sum
);
    wire [15:0] cout,con2;
    wire [15:0]alt_sum1, alt_sum2;
    add16 adder1(a[15:0], b[15:0], 0, sum[15:0], cout);
    add16 adder_sel1(a[31:16], b[31:16], 0, alt_sum1, con2);
    add16 adder_sel2(a[31:16], b[31:16], 1, alt_sum2, con2);
    
    always @(cout, alt_sum1, alt_sum2) begin
        case(cout)
            0 : sum[31:16] = alt_sum1;
            1 : sum[31:16] = alt_sum2;
        endcase
    end

endmodule

//adder substractor
module top_module(
    input [31:0] a,
    input [31:0] b,
    input sub,
    output [31:0] sum
);
	//An XOR gate can also be viewed as a programmable inverter, where one input controls whether
    //the other should be inverted. 
    
    wire wire1;
    wire [31:0]b_xor;
    
    assign b_xor = {32{sub}}^b; 
    add16 adder1(a[15:0], b_xor[15:0], sub, sum[15:0], wire1);
    add16 adder2(a[31:16], b_xor[31:16], wire1, sum[31:16]);
    
    
endmodule

//sequential logic

//scan chain? 
// series of flip flops / scan flops connected in a 
//serial fashion such that you can shift test data in and
//out when in scan mode/
// in normal (functional) mode, the flip flops behave as regular flops
// the scan operation typically has three modes
// shift, capture and shift out
// shift -> you shift in a test vector
// capture -> you can apply one or more clock pulses so that internal logic transitions
//shift out is to read the results

// basically scan chain is 
// modified flip flops, that have extra inputs or outputs so 
// they can be chained together

module top_module (
    input clk,    // Clocks are used in sequential circuits
    input d,
    output reg q );//

    always @ (posedge clk) begin
    	q <= d;
    
    end

endmodule

//dff + gate
module top_module (
    input clk,
    input in, 
    output out);
	
    always @ (posedge clk) begin
    	out <= out ^ in;
    end
endmodule

//mux&dff
module top_module (
	input clk,
	input L,
	input r_in,
	input q_in,
	output reg Q);
    
    always @ (posedge clk) begin
        case (L)
            1'b0 : Q <= q_in;
            1'b1 : Q <= r_in;
        endcase    
    end

endmodule

//mux and dff2
module top_module (
    input clk,
    input w, R, E, L,
    output Q
);
    wire [1:0] con;
    assign con = {E,L};
	always @ (posedge clk) begin
        case (con)
            2'b00 : Q <= Q;
            2'b01 : Q <= R;
			2'b10 : Q <= w;
            2'b11 : Q <= R;        
        endcase    
    end

endmodule


//detetct an edge
module top_module (
    input clk,
    input [7:0] in,
    output [7:0] pedge
);
    reg [7:0]intermediate;
    
    always @ (posedge clk) begin
        intermediate <= in;
        pedge        <= (~intermediate) & in;
    end

endmodule

//detect both edges
module top_module (
    input clk,
    input [7:0] in,
    output [7:0] anyedge
);
  	reg [7:0]intermediate;
    
    always @ (posedge clk) begin
        intermediate   <= in;
        anyedge        <= intermediate ^ in;
    end
endmodule

//double edge triggered flip flop
module top_module (
    input clk,
    input d,
    output q
);
    reg q1,q2;
    always @ (posedge clk) begin
    	q1 <= q2^d; 
    end
    
    always @ (negedge clk) begin
    	q2 <= q1^d; 
    end
    
    assign q = q1^q2; 
endmodule

//8 d flips flops

module top_module (
    input clk,
    input [7:0] d,
    output [7:0] q
);
    always @ (posedge clk) begin
    	q <= d;
    end
endmodule

//dff with reset
module top_module (
    input clk,
    input reset,            // Synchronous reset
    input [7:0] d,
    output [7:0] q
);
	always @ (posedge clk) begin
        //this is an active high  synchronous reset
        //means the block runs whenever there is a rising edge of the clock
        // the if reset is 1 at that clock edge
        // the output q is forced to 0 (8'b0)
        //else -> if the reset is 0
        // if reset is 0, the input value d is stored into q
        if (reset) q<=8'b0;
        else q <= d;
    end
endmodule

//dff with reset value (negedge)
module top_module (
    input clk,
    input reset,
    input [7:0] d,
    output [7:0] q
);
    always @ (negedge clk) begin
        //this is an active high  synchronous reset
        // when reset is asserted (1) , q is set to 8'hex34, 52 in decimal
        //with every falling edge of clk
        //if reset =1 , 8 becomes 0x34
        //if reset =0, q takes the new value from d
        if (reset==1'b1) q<=8'h34;
        else q <= d;
    end
endmodule

//dff with async reset  
 module top_module (
    //clocking signal cannot  be referenced anywhere in the always block 
    input clk,
    input areset,   // active high asynchronous reset
    input [7:0] d,
    output [7:0] q
);
    always @ (posedge clk or posedge areset ) begin
        //this is an active high  asynchronous reset
        if (areset==1'b1) q<= 1'b0;
        
        else q <= d;
    end
endmodule

//dff with byte enable
module top_module (
    input clk,
    input resetn,
    input [1:0] byteena,
    input [15:0] d,
    output [15:0] q
);
	always @ (posedge clk) begin
        //this is an active high  synchronous reset
        if (resetn==1'b0) q<= 1'b0;
        else begin
            case(byteena)
				2'b00: q       <= q;
                2'b01: q[7:0]  <= d[7:0];
                2'b10: q[15:8] <= d[15:8];
                2'b11: q       <= d;
            endcase
        end
    end	
endmodule

//d latch
module top_module (
    input d, 
    input ena,
    output q);
	
    //Latches are level-sensitive (not edge-sensitive) circuits, so in an always block, they use level-sensitive sensitivity lists.
	//However, they are still sequential elements, so should use non-blocking assignments.
	//A D-latch acts like a wire (or non-inverting buffer) when enabled, and preserves the current value when disabled.

    always @ (*) begin
        // the @(*) means combinational logic 
        // sensitive to any change of d
        //or ena
        //inside the loop 
        //enable is 1, so we assign q=d
        // of enable is 0, we will do nothing ( no assignment)
        if (ena) q<=d;
    end

endmodule

//dff
module top_module (
    input clk,
    input d, 
    input ar,   // asynchronous reset
    output q);
    
    always @ (posedge clk, posedge ar) begin
        if (ar) q<=1'b0;
        else q<=d;
        
    end
endmodule


//dff2
module top_module (
    input clk,
    input d, 
    input r,   // synchronous reset
    output q);
    always @ (posedge clk) begin
        if (r) q <= 1'b0;
        else   q <= d;
    end
endmodule

//dff +gate
//mux & dff
//mux and dff
//dff abd gates
//create circuit from truth table
//detect an edge
//detect both edges
//edge capture register
//dual edge triggerd fli[ flop]



//COUNTERS

// four bit binary counter
module top_module (
    input clk,
    input reset,      // Synchronous active-high reset
    output [3:0] q);

    always @ (posedge clk) begin

        // trigger condition , should always execute at the rising edge
        // reset case : reset =1, then q is set to 4'b0 (decimal = o)
        // since the reset is asynchronous, this only happens at a clock edge
        // the normal case is reset =0. then q is incremented by q<=q+1
        // the increment makes it a counter
        // so we start at zero when reset is active 
        // increments on every clock cycle when reset is low
        // because q is 4 bits wide , it counts from 0 to 15
        // then wraps around to 0 (OVERFLOW)
        if (reset) q <= 4'd0;
        else q <= q+4'd1;
    end
endmodule

//decade counter

module top_module (
    input clk,
    input reset,        // Synchronous active-high reset
    output [3:0] q);
    
    always @ (posedge clk) begin
        //reset = 1 at a riisng edge, q becomes 0 
        //it wont change immediately, its gonna wait for the clock
        //the wrap condition is that q=9, 4'd9, at a rising edge thee
        // next value will be 0 to avoid our overflow

        if (reset) q <= 4'd0;
        else if (q == 4'd9) q<= 4'd0;
        else q <= q+4'd1;
    end
endmodule

//decade counter (1 to 10)
module top_module (
    input clk,
    input reset,
    output [3:0] q);

    always @ (posedge clk) begin
        if (reset) q <= 4'd1;
        else if (q == 4'd10) q<= 4'd1;
        else q <= q+4'd1;
    end
    
endmodule

//slow decade counter
module top_module (
    input clk,
    input slowena,
    input reset,
    output [3:0] q);

    always @ (posedge clk) begin
        if (reset) q <= 4'd0;
        else if (slowena) begin
        	if (q == 4'd9) q<= 4'd0;
        	else q <= q+4'd1;
        end
    end
    
endmodule

// combinationals 

// wire
module top_module (
    input in,
    output out);
	assign out = in;
    
endmodule
//gnd
module top_module (
    output out);
	assign out = 1'b0;
endmodule
//nor
module top_module (
    input in1,
    input in2,
    output out);
    assign out = ~(in1|in2);
endmodule
//another gate
module top_module (
    input in1,
    input in2,
    output out);
    assign out = ~(in1|in2);
endmodule
//two gates
module top_module (
    input in1,
    input in2,
    output out);
    assign out = ~(in1|in2);
endmodule
//more logic gates
module top_module( 
    input a, b,
    output out_and,
    output out_or,
    output out_xor,
    output out_nand,
    output out_nor,
    output out_xnor,
    output out_anotb
);
	assign out_and   = a && b;
    assign out_or    = a || b;
    assign out_xor   = a ^ b;
    assign out_nand  = ~(a&&b);
    assign out_nor   = ~(a||b);
    assign out_xnor  = ~(a^b);
    assign out_anotb =  a&&~b;
endmodule
//7420 chip
module top_module ( 
    input p1a, p1b, p1c, p1d,
    output p1y,
    input p2a, p2b, p2c, p2d,
    output p2y );
	
    assign p1y = ~(p1a && p1b && p1c && p1d);
    assign p2y = ~(p2a && p2b && p2c && p2d);

endmodule
//truth tables
module top_module ( 
    input p1a, p1b, p1c, p1d,
    output p1y,
    input p2a, p2b, p2c, p2d,
    output p2y );
	
    assign p1y = ~(p1a && p1b && p1c && p1d);
    assign p2y = ~(p2a && p2b && p2c && p2d);

endmodule
//two bit equality
module top_module ( input [1:0] A, input [1:0] B, output z ); 
    assign z = (A==B);

endmodule
// simple circuit a
module top_module (input x, input y, output z);
    assign z = (x^y) & x;
endmodule
//simple circuit b
module top_module ( input x, input y, output z );
    assign z= ~(x^y);
endmodule
//combine a and b
module top_module (input x, input y, output z);
    wire z1, z2, z3, z4,z5,z6;
    
    A IA1(x,y,z1);
    B IB1(x,y,z2);
    A IA2(x,y,z3);
    B IB2(x,y,z4);
    
    assign z5 = z1||z2;
    assign z6 = z3&&z4;
    assign  z = z5^z6;
endmodule

module B( input x, input y, output z );
    assign z= ~(x^y);
endmodule

module A(input x, input y, output z);
    assign z = (x^y) & x;
endmodule

//ring or vibrate
module top_module (
    input ring,
    input vibrate_mode,
    output ringer,       // Make sound
    output motor         // Vibrate
);
    assign motor  = vibrate_mode && ring;
    assign ringer = (~vibrate_mode) && ring;
endmodule
//thermostat
module top_module (
    input too_cold,
    input too_hot,
    input mode,
    input fan_on,
    output heater,
    output aircon,
    output fan
); 
	assign heater = mode && too_cold;
    assign aircon = (~mode) && too_hot;
    assign fan    = aircon || heater || fan_on;
endmodule
//3 bit population vcpunt
module top_module( 
    input [2:0] in,
    output [1:0] out );
    integer i,count;
	always @ * begin
        count = 0;
        for (i=0; i<3;i=i+1) begin
            if (in[i]==1'b1) count=count+1;
        end
        out = count;
    end
endmodule
//gates and vectors
module top_module( 
    input [3:0] in,
    output [2:0] out_both,
    output [3:1] out_any,
    output [3:0] out_different );
	
    assign out_both      = in[2:0] & in[3:1];//here bits of input vector is shifted right 
    									//and bitwise and is performed to obtain the required output
    assign out_any       = in[3:1] | in[2:0];
    assign out_different = in ^ {in[0],in[3:1]};
    
endmodule
//even longer vectors
module top_module( 
    input [99:0] in,
    output [98:0] out_both,
    output [99:1] out_any,
    output [99:0] out_different );
	
    assign out_both      = in[98:0] & in[99:1];//here bits of input vector is shifted right 
    									//and bitwise and is performed to obtain the required output
    assign out_any       = in[99:1] | in[98:0];
    assign out_different = in ^ {in[0],in[99:1]};
 
endmodule

//multiplexers
//2 to 1 mux
module top_module( 
    input a, b, sel,
    output out ); 
	
    assign out  = sel?b:a;
endmodule
//2. to 1 bus mux
module top_module( 
    input [99:0] a, b,
    input sel,
    output [99:0] out );
	assign out = sel?b:a;
endmodule
// 9 to 1 mux
module top_module( 
    input [15:0] a, b, c, d, e, f, g, h, i,
    input [3:0] sel,
    output [15:0] out );
  
    always @ * begin
  
        case (sel)
            4'b0000 : out = a;
            4'b0001 : out = b;
            4'b0010 : out = c;
            4'b0011 : out = d;
            4'b0100 : out = e;
            4'b0101 : out = f;
            4'b0110 : out = g;
            4'b0111 : out = h;
            4'b1000 : out = i;
            default : out = {16{1'b1}};
        endcase
    end

endmodule
// 256 to 1 mux
//256 to 1 4 bit mux
module top_module( 
    input [1023:0] in,
    input [7:0] sel,
    output [3:0] out );
	
    integer range;
    wire [7:0]con1; 
    
    always @ (*) begin
        range = sel;
    	//max_lim = sel;
        //min_lim = ;
        //con1 = sel+sel+sel+sel; 
        out  = in[sel*4 +:4]; //vector[LSB+:width]
        
    end
endmodule

//arithmetic ciruicts 
//half adder
module top_module( 
    input a, b,
    output cout, sum );
	
    assign sum  = a^b;
    assign cout = a&b;
        
endmodule
//full adder
module top_module( 
    input a, b,
    output cout, sum );
	
    assign sum  = a^b;
    assign cout = a&b;
        
endmodule
//3 bit binary adder
module top_module( 
    input a, b,
    output cout, sum );
	
    assign sum  = a^b;
    assign cout = a&b;
        
endmodule
//adder
module top_module (
    input [3:0] x,
    input [3:0] y, 
    output [4:0] sum);
    wire [3:0]cout;
    
    FA FA1(x[0],y[0],0,cout[0],sum[0]);
    FA FA2(x[1],y[1],cout[0],cout[1],sum[1]);
    FA FA3(x[2],y[2],cout[1],cout[2],sum[2]);
    FA FA4(x[3],y[3],cout[2],sum[4],sum[3]);
endmodule

module FA( 
    input a, b, cin,
    output cout, sum );
    
	assign cout = a&b | b&cin | a&cin;
	assign sum  = a^b^cin;
endmodule
//100 bit binary adder
module top_module( 
    input [99:0] a, b,
    input cin,
    output cout,
    output [99:0] sum );

    genvar i;
    wire [98:0]con_vect;
    one_bit_FA FA1(a[0],b[0],cin,con_vect[0],sum[0]);
    one_bit_FA FA2(a[99],b[99],con_vect[98],cout,sum[99]);
    
    //this is a generte block
    //The loop generate construct provides an easy and concise method to create multiple instances 
    //of module items such as module instances, assign statements, assertions, interface instances 
    //In essence generate block is a special type of for loop with the loop index variable of datatype genvar.
    generate
        for (i=1; i<99; i=i+1) begin : Full_adder_block
            one_bit_FA FA(a[i],b[i],con_vect[i-1],con_vect[i],sum[i]);
    end
    
      
    endgenerate
    
endmodule

module one_bit_FA(
    input a,b,
    input cin,
    output cout,sum);
	
    assign sum  = a^b^cin;
    assign cout = (a&b)|(b&cin)|(cin&a);
endmodule
//signed addition overflow
module top_module (
    input [7:0] a,
    input [7:0] b,
    output [7:0] s,
    output overflow
); //
 	//2's complement for a binary number is found by inverting the numbers and adding 1
    //	i.e: 2'scomplement of 0011 is : 1100+0001 =  1101
    //
    //Also remember that MSB of the 2's complement number represents  the sign. i.e if MSB is one then the number is -ve
    //	i.e: 1101 = -8+4+0+1=-3
    //
    //If 2= 0010 then -2= 1101+1 = 1110
    //Also 2+(-2) = 1111 (This property holds for all the numbers)
    //
    //While adding two 2's complement numbers, overflow can be detected two ways:
    //	1. If carryout and crry-on to  MSB are different then overflow occured
    //  2. If both numbers are +ve and result is-ve or vise versa, overflow occurs
    
    assign s = a+b;
    assign overflow = a[7]&&b[7]&&(~s[7]) || (~a[7])&&(~b[7])&&(s[7]); 

endmodule



module top_m( 
    input a, b, cin,
    output cout, sum );
    
	assign cout = a&b | b&cin | a&cin;
	assign sum  = a^b^cin;
endmodule
// 4 digit BDC adder
module top_module( 
    input [15:0] a, b,
    input cin,
    output cout,
    output [15:0] sum );
    wire [2:0]con1;
    
    //in BCD addition, if sum of digit BCD numbers is greater than 9 then we should further add 6 to the result to obtain the correct solution
    //ex : 5+3 = 8  = 0000 1000 obtained by 0101+0011      
    //     8+9 = 17 = 0001 0111 obtained by 1000+1001+0110
 
    bcd_fadd B_add1(a[3:0],b[3:0],cin,con1[0],sum[3:0]);
    bcd_fadd B_add2(a[7:4],b[7:4],con1[0],con1[1],sum[7:4]);
    bcd_fadd B_add3(a[11:8],b[11:8],con1[1],con1[2],sum[11:8]);
    bcd_fadd B_add4(a[15:12],b[15:12],con1[2],cout,sum[15:12]);

endmodule



