# BSD 3-Clause License
#
# Copyright (c) 2016, 2017, The University of Sydney. All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
#
# * Redistributions of source code must retain the above copyright notice, this
#   list of conditions and the following disclaimer.
#
# * Redistributions in binary form must reproduce the above copyright notice,
#   this list of conditions and the following disclaimer in the documentation
#   and/or other materials provided with the distribution.
#
# * Neither the name of the copyright holder nor the names of its
#   contributors may be used to endorse or promote products derived from
#   this software without specific prior written permission.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
# AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
# IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
# DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
# FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
# DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
# SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
# CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
# OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
# OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

"""exporter.py: abstract classes for exporting decompiler state"""

import abc
import logging
import os

import src.vandal.cfg as cfg
import src.vandal.function as function
import src.vandal.opcodes as opcodes
import src.vandal.patterns as patterns
import src.vandal.tac_cfg as tac_cfg
import src.vandal.memtypes as memtypes
import json


class Analysis(abc.ABC):
    def __init__(self, source: object):
        """
        Args:
          source: object instance to be exported
        """
        self.source = source

    @abc.abstractmethod
    def analyze(self):
        """
        Exports the source object to an implementation-specific format.
        """

class CostAnalysis(Analysis):
    """
    Generates a dot file for drawing a pretty picture of the given CFG.

    Args:
      cfg: source CFG to be exported to dot format.
    """

    def __init__(self, cfg: cfg.ControlFlowGraph):
        super().__init__(cfg)

    def extract_fun(block):
        arg_num = int(str(block).count('CALLDATALOAD')/2)
        entry = str(hex(block.entry)) + '-' + str(arg_num)
        return entry


    def analyze(self):
        """
        Export the CFG to a dot file.

        Certain blocks will have coloured outlines:
          Green: contains a RETURN operation;
          Blue: contains a STOP operation;
          Red: contains a THROW, THROWI, INVALID, or missing operation;
          Purple: contains a SELFDESTRUCT operation;
          Orange: contains a CALL, CALLCODE, or DELEGATECALL operation;
          Brown: contains a CREATE operation.

        A node with a red fill indicates that its stack size is large.

        Args:
          out_filename: path to the file where dot output should be written.
                        If the file extension is a supported image format,
                        attempt to generate an image using the `dot` program,
                        if it is in the user's `$PATH`.
        """
        cfg = self.source
        worker = cfg.root
        work_list = [worker]
        public_fun_list = cfg.function_extractor.public_functions
        private_fun_list = cfg.function_extractor.private_functions
        # No private functions for now.
        # assert len(private_fun_list) == 0
        public_methods = []
        private_methods = []
        cfg_json = {}
        for func in public_fun_list:
            # print('org public method:', hex(func.start_block.entry))
            # print('==============>')

            if len(func.start_block.succs) == 1 or (not ('CALLVALUE' in str(func.start_block))):
                # arg_num = int(str(func.start_block).count('CALLDATALOAD')/2)
                arg_num = int(str(func.start_block).count('CALLDATALOAD')/2)
                entry = str(hex(func.start_block.entry)) + '-' + str(arg_num)
                # print('debug1:', entry)
                public_methods.append(entry)
               # public_methods.append(str(hex(func.start_block.entry)) + '-' + str(arg_num))
                # public_methods.append(extract_fun(func.start_block))
                # print(extract_fun(func.start_block))
                # print(str(hex(func.start_block.entry)) + '-' + str(arg_num))
            else:
                for suc in func.start_block.succs:
                    if len(suc.succs) > 0:
                        # print('adding public:', hex(suc.entry))
                        # arg_num = int(str(suc).count('CALLDATALOAD')/2)
                        # public_methods.append(str(hex(suc.entry)) + '-' + str(arg_num))
                        # public_methods.append(extract_fun(suc))
                        arg_num = int(str(suc).count('CALLDATALOAD')/2)
                        entry = str(hex(suc.entry)) + '-' + str(arg_num)
                        # print('debug2:', entry)
                        public_methods.append(entry)
                        # print(entry)
                        # print(str(hex(suc.entry)) + '-' + str(arg_num))
                        # print(extract_fun(suc))
                        # break

        for func in private_fun_list:
            if len(func.start_block.succs) == 1:
                private_methods.append(hex(func.start_block.entry))
                continue
            for suc in func.start_block.succs:
                if len(suc.succs) > 0:
                    # print('adding private:', hex(suc.entry))
                    private_methods.append(hex(suc.entry))
                    break


        cfg_json['name'] = 'ControlFlowGraph'
        cfg_json['root'] = hex(cfg.root.entry)
        cfg_json['public_methods'] = public_methods
        cfg_json['private_methods'] = private_methods
        blocks = []

        for blk in cfg.blocks:
            blk_obj = {}
            blk_obj['address'] = hex(blk.entry)
            inst_list = []
            pred_list = []
            succ_list = []
            # print('block address=====:', hex(blk.entry), 'entry@', blk.entry_stack, 'exit@', blk.exit_stack)

            for tac_op in blk.tac_ops:
                # print('inst--->', tac_op)
                inst_str = str(tac_op)
                if 'S0' in str(tac_op) and len(blk.preds) == 1:
                    myped = blk.preds[0]
                    s1 = myped.exit_stack.peek(0)
                    s2 = blk.entry_stack.peek(0)
                    if not str(s1) == str(s2):
                        inst_str = str(tac_op).replace(str(s2), str(s1))

                inst_list.append(inst_str)

            for su in blk.preds:
                pred_list.append(hex(su.entry))

            for pr in blk.succs:
                if len(blk.exit_stack) == len(pr.entry_stack):
                    for idx in range(len(pr.entry_stack)):
                        rhs = blk.exit_stack.peek(idx)
                        lhs = pr.entry_stack.peek(idx)
                        if (not isinstance(rhs, memtypes.MetaVariable)) and isinstance(lhs, memtypes.MetaVariable):
                            extra_inst = '0xff: ' + str(lhs) + ' = ' + str(rhs)
                            last_inst = inst_list[-1]
                            last_inst_str = str(last_inst)
                            if 'JUMP' in last_inst_str or 'THROW' in last_inst_str:
                                inst_list.insert(-1, extra_inst)
                            else:
                                inst_list.append(extra_inst)
                            # print('generate new pair:*****', inst_list, last_inst, ('JUMP' in str(last_inst)))
                succ_list.append(hex(pr.entry))

            blk_obj['insts'] = inst_list
            blk_obj['preds'] = pred_list
            blk_obj['succs'] = succ_list
            blocks.append(blk_obj)

        cfg_json['blocks'] = blocks
        return json.dumps(cfg_json)
        # with open('cfg.json', 'w') as outfile:
        #     json.dump(cfg_json, outfile)


        # G = cfg.nx_graph()

        # # Colour-code the graph.
        # returns = {block.ident(): "green" for block in cfg.blocks
        #            if block.last_op.opcode == opcodes.RETURN}
        # stops = {block.ident(): "blue" for block in cfg.blocks
        #          if block.last_op.opcode == opcodes.STOP}
        # throws = {block.ident(): "red" for block in cfg.blocks
        #           if block.last_op.opcode.is_exception()}
        # suicides = {block.ident(): "purple" for block in cfg.blocks
        #             if block.last_op.opcode == opcodes.SELFDESTRUCT}
        # creates = {block.ident(): "brown" for block in cfg.blocks
        #            if any(op.opcode == opcodes.CREATE for op in block.tac_ops)}
        # calls = {block.ident(): "orange" for block in cfg.blocks
        #          if any(op.opcode.is_call() for op in block.tac_ops)}
        # color_dict = {**returns, **stops, **throws, **suicides, **creates, **calls}
        # nx.set_node_attributes(G, "color", color_dict)
        # filldict = {b.ident(): "white" if len(b.entry_stack) <= 20 else "red"
        #             for b in cfg.blocks}

