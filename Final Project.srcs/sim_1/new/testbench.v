`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: Aly Ghallab 
// 
// Create Date: 05/04/2023 08:34:58 PM
// Design Name: 
// Module Name: testbench
// Project Name: CMPEN 331 Final Project
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////


module testbench();
    reg clk;
    reg clrn;
    wire [31:0] instr;
    wire [31:0] pc;
    wire [31:0] alu;
    
    Datapath Datapath_instr1 (clk, clrn, inst, pc, alu);
    initial
    begin
        clk = 0;
        clrn = 1;
    end
    always
    begin
        #5;
        clk = ~clk;
    end
endmodule
