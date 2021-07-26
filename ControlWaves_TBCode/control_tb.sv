
module control_tb(	
	 output logic         PCWrite,
	 output logic         MemWrite,
	 output logic         RegWrite,
	 output logic         IRWrite,
	 output logic         AdrSrc,
	 output logic [1:0]   RegSrc,
	 output logic         ALUSrcA,
	 output logic [1:0]   ALUSrcB,
	 output logic [1:0]   ResultSrc,
	 output logic [1:0]   ImmSrc,
	 output logic [1:0]   ALUControl);
	 
	 
	 
	logic clk,reset;
	logic [31:0] instruction;
	logic [3:0] ALUFlags;
		
	initial
		begin
			reset <= 1; #100; reset <= 0;
			
			ALUFlags <= 0000;
			instruction <= 32'b11100000010011110000000000001111; // SUB R0,R15,R15
			#400;
			
			
			instruction <= 32'b10110010100001010111000000000001; // ADDLT R7,R5,R1 (RegWrite should be 0 ) 
			#400;
			
			instruction <= 32'b11100001100001110100000000000010; // ORR R4,R7,R2
			#400;
			
			instruction <= 32'b11100000000000110101000000000100; // AND R5,R3,R4
			#400;
			
			instruction <= 32'b11100000100001010101000000000100; // ADD R5,R5,R4
			#400;
			
			instruction <= 32'b11101010000000000000000000000001; // B END (Always Taken) 
			#300;
		
			instruction <= 32'b00001010000000000000000000001100; // BEQ END (Shouldnt be taken)
			ALUFlags <= 0001;
			#300;
			
			instruction <= 32'b11100101100000110111000001010100; //STR R7,[R3,#84] 
			#400;
			
			instruction <= 32'b11100101100100000010000001100000; //LDR R2, [R0,#96]
			#500;
			
		end	
		
	always
		begin
			clk <= 1; #50; clk <= 0; #50;
		end

	controller cu(clk,reset, instruction[31:12] , ALUFlags, PCWrite,MemWrite,RegWrite,IRWrite,AdrSrc,RegSrc,ALUSrcA,ALUSrcB,ResultSrc,ImmSrc,ALUControl);
	
endmodule


module controller(input  logic         clk,
                  input  logic         reset,
                  input  logic [31:12] Instr,
                  input  logic [3:0]   ALUFlags,
						
                  output logic         PCWrite,
                  output logic         MemWrite,
                  output logic         RegWrite,
                  output logic         IRWrite,
                  output logic         AdrSrc,
                  output logic [1:0]   RegSrc,
                  output logic         ALUSrcA,
                  output logic [1:0]   ALUSrcB,
                  output logic [1:0]   ResultSrc,
                  output logic [1:0]   ImmSrc,
                  output logic [1:0]   ALUControl);
        logic [1:0] FlagW;
		  logic PCS, NextPC, RegW, MemW;
	
  decode decoder(clk, reset, Instr[27:26], Instr[25:20], Instr[15:12],
             FlagW, PCS, NextPC, RegW, MemW,
             IRWrite, AdrSrc, ResultSrc, ALUSrcA, 
             ALUSrcB, ImmSrc, RegSrc, ALUControl);
				 
  condlogic condlog(clk, reset, Instr[31:28], ALUFlags,
               FlagW, PCS, NextPC, RegW, MemW,
               PCWrite, RegWrite, MemWrite);            
		

endmodule



module decode(input  logic       clk, reset,
              input  logic [1:0] Op,
              input  logic [5:0] Funct,
              input  logic [3:0] Rd,
              output logic [1:0] FlagW,
              output logic       PCS, NextPC, RegW, MemW,
              output logic       IRWrite, AdrSrc,
              output logic [1:0] ResultSrc,
				  output logic       ALUSrcA,
				  output logic [1:0] ALUSrcB, 
              output logic [1:0] ImmSrc, RegSrc, ALUControl);

  // ADD CODE HERE
  // Implement a microprogrammed controller
  // using a control memory (ROM).
  logic Branch,ALUOp;
  
  
  
	//ALU Decoder
  	always_comb
		if (ALUOp) 
			begin
				case(Funct[4:1])
					4'b0100: ALUControl = 2'b00; // ADD
					4'b0010: ALUControl = 2'b01; // SUB
					4'b0000: ALUControl = 2'b10; // AND
					4'b1100: ALUControl = 2'b11; // ORR
					default: ALUControl = 2'bXX; // unimplemented
				endcase

				FlagW[1] = Funct[0];
				FlagW[0] = Funct[0] & (ALUControl == 2'b00 | ALUControl == 2'b01);
			end 
		else 
			begin
				ALUControl = 2'b00; // add for non-DP instructions
				FlagW = 2'b00; // don't update Flags
			end
			
			
			
	//PC Logic
	assign PCS = ((Rd == 4'b1111) & RegW) | Branch;
  
  
  
  
	// Instr Decoder 
	assign RegSrc = Op == 2'b00 ? (Funct[5] == 1'b1 ? 2'bX0 : 2'b00) : 
								(Op == 2'b01 ? (Funct[0] == 1'b1 ? 2'bX0 : 2'b10) : 
									(Op == 2'b10 ? 2'bX1 : 2'bXX));
	assign ImmSrc = Op;
	
	
	
	// Microprogrammed Control
	mpControl mpc(clk,reset,Op,Funct,NextPC,RegW,MemW,IRWrite,AdrSrc,ALUSrcA,Branch,ALUOp,ResultSrc,ALUSrcB);
		
endmodule


module mpControl(input logic clk, reset,
				   input logic [1:0] Op,
				   input logic [5:0] Funct,
				   output logic NextPC, RegW, MemW, IRWrite, AdrSrc, ALUSrcA, Branch, ALUOp,
				   output logic [1:0] ResultSrc, ALUSrcB);
					
			logic [29:0] cw;			
			logic [4:0] adr ; 
			
			
			
			controlMemory cm( adr , cw );
			branchLogic bl(clk,reset,cw,Op,Funct,adr);
			
			
			// assign outputs here 
			assign {Branch,ALUOp,NextPC,RegW,MemW,IRWrite,AdrSrc,ResultSrc,ALUSrcA,ALUSrcB} =
						{ cw[29:28],cw[24:15] } ;
			
							
endmodule 



module branchLogic( input logic clk,reset,
						  input logic [29:0] cw,
						  input logic [1:0] op,
						  input logic [5:0] funct,
						  output logic [4:0] nextAdr);
						 

			always_ff@(posedge clk,posedge reset)
				if(reset)
					nextAdr <= 5'b11111;
				else 
					begin 
						case( cw[4:0] ) 
							5'b01010:
								nextAdr <= nextAdr+5'b00001;
								
							5'b01011:
								if(op==2'b01)
									nextAdr <= 5'b00010;
								else if(op==2'b10)
									nextAdr <= 5'b01001;
								else
									if(funct[5]== 0)
										nextAdr <= 5'b00110;
									else
										nextAdr <= 5'b00111;
										
										
							5'b01100:
								if( funct[0]==0)
										nextAdr <= 5'b00101;
								else
										nextAdr <= 5'b00011;
										
										
							default:
								nextAdr <= cw[4:0];
							endcase
						end
						 
endmodule




module controlMemory(input logic[4:0] adr,
			  output logic [29:0] dout);
	always_comb
		case(adr)
			// 01010 : Increment 
			// 01011 : Instruction Register
			// 01100 : ConditionCheck
			
			5'b00000: dout = 30'b000001001010110xxxxxx_xxxx_01010;
			
			5'b00001: dout = 30'b000000000x10110xxxxxx_xxxx_01011;
			
			5'b00010: dout = 30'b000000000xxx001xxxxxx_xx0x_01100;
			
			5'b00011: dout = 30'b000000100100xxxxxxxxx_xxxx_01010;
			
			5'b00100: dout = 30'b000000100x01xxxxxxxxx_xxxx_00000;
			
			5'b00101: dout = 30'b000000010100xxxxxxxxx_xxxx_00000;
			
			5'b00110: dout = 30'b010000000xxx000xxxxxx_xxxx_01000;
			
			5'b00111: dout = 30'b010000000xxx001xxxxxx_xxxx_01000;
			
			5'b01000: dout = 30'b000000100x00xxxxxxxxx_xxxx_00000;
			
			5'b01001: dout = 30'b100000000x10001xxxxxx_xxxx_00000;
			
			default: dout= 0;
			
		endcase 
	
endmodule

module condlogic(input  logic       clk, reset, 
                 input  logic [3:0] Cond, 
                 input  logic [3:0] ALUFlags, 
                 input  logic [1:0] FlagW, 
                 input  logic       PCS, NextPC, RegW, MemW, 
                 output logic       PCWrite, RegWrite, MemWrite); 
 
  logic [1:0] FlagWrite; 
  logic [3:0] Flags; 
  logic       CondEx, CondExDelayed; 
 
  flopenr #(2) flagreg1(clk, reset, FlagWrite[1], ALUFlags[3:2],  
Flags[3:2]); 

  flopenr #(2) flagreg0(clk, reset, FlagWrite[0], ALUFlags[1:0],  
Flags[1:0]); 
 
  // write controls are conditional 
  condcheck cc(Cond, Flags, CondEx); 
  flopr #(1)condreg(clk, reset, CondEx, CondExDelayed); 
  assign FlagWrite = FlagW & {2{CondEx}}; 
  assign RegWrite  = RegW  & CondExDelayed; 
  assign MemWrite  = MemW  & CondExDelayed; 
  assign PCWrite   = (PCS  & CondExDelayed) | NextPC; 
  
endmodule     



module condcheck(input  logic [3:0] Cond, 
                 input  logic [3:0] Flags, 
                 output logic       CondEx); 
 
  logic neg, zero, carr, overflow, ge; 
   
  assign {neg, zero, carr, overflow} = Flags; 
  assign ge = (neg == overflow); 
                   
  always_comb 
    case(Cond) 
      4'b0000: CondEx = zero;             // EQ 
      4'b0001: CondEx = ~zero;            // NE 
      4'b0010: CondEx = carr;             // CS 
      4'b0011: CondEx = ~carr;            // CC 
      4'b0100: CondEx = neg;              // MI 
 

      4'b0101: CondEx = ~neg;             // PL 
      4'b0110: CondEx = overflow;         // VS 
      4'b0111: CondEx = ~overflow;        // VC 
      4'b1000: CondEx = carr & ~zero;     // HI 
      4'b1001: CondEx = ~(carr & ~zero);  // LS 
      4'b1010: CondEx = ge;               // GE 
      4'b1011: CondEx = ~ge;              // LT 
      4'b1100: CondEx = ~zero & ge;       // GT 
      4'b1101: CondEx = ~(~zero & ge);    // LE 
      4'b1110: CondEx = 1'b1;             // Always 
      default: CondEx = 1'bx;             // undefined 
    endcase
	 
endmodule 


module flopr #(parameter WIDTH = 8) 
              (input  logic             clk, reset, 
               input  logic [WIDTH-1:0] d,  
               output logic [WIDTH-1:0] q); 
 
  always_ff @(posedge clk, posedge reset) 
    if (reset) q <= 0; 
    else       q <= d; 
endmodule 


module flopenr #(parameter WIDTH = 8) 
                (input  logic             clk, reset, en, 
                 input  logic [WIDTH-1:0] d,  
                 output logic [WIDTH-1:0] q); 
 
  always_ff @(posedge clk, posedge reset) 
    if (reset)   q <= 0;

    else if (en) q <= d; 
endmodule 

module mux3 #(parameter WIDTH = 8)
             (input  logic [WIDTH-1:0] d0, d1, d2,
              input  logic [1:0]       s, 
              output logic [WIDTH-1:0] y);

  assign y = s[1] ? d2 : (s[0] ? d1 : d0); 
endmodule