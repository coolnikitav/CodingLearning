# Clean previous simulation declarations
file delete -force sim.wdb
file delete -force xsim.dir

# Compile SV testbench file
exec C:/Xilinx/Vivado/2023.2/bin/xvlog --sv C:\eng_apps\vivado_rojects\LC3\LC3.srcs\sim_1\new\decode_tb.sv

# Compile the Verilog design file
exec C:/Xilinx/Vivado/2023.2/bin/xvlog C:\eng_apps\vivado_rojects\LC3\LC3.srcs\sources_1\new\decode.v

# Elaborate decode_tb
exec C:/Xilinx/Vivado/2023.2/bin/xelab -debug typical work.decode_tb -sv_lib C:\eng_apps\vivado_rojects\LC3\LC3.ref_models\decode\LC3DecodeRefModel

# Run the simulation
exec C:/Xilinx/Vivado/2023.2/bin/xsim work.decode_tb -gui