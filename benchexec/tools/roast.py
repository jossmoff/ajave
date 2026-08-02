# This file is part of BenchExec, a framework for reliable benchmarking:
# https://github.com/sosy-lab/benchexec
#
# SPDX-FileCopyrightText: 2026 Joss Sheridan-Sheridan
# SPDX-License-Identifier: Apache-2.0

"""
BenchExec tool-info module for roast, an SV-COMP Java bytecode verifier.

roast compiles Java source (or loads pre-compiled .class files), lifts them
to an internal IR, runs a portfolio of engines (concrete BMC, SMT BMC,
interval abstract interpretation), and certifies every FALSE by replaying
the witness on a real JVM before reporting.

Usage in a BenchExec XML configuration::

    <benchmark tool="roast" ...>
      <tasks>
        <include>../sv-benchmarks/java/jbmc-regression/**/*.yml</include>
        <propertyfile>../sv-benchmarks/java/properties/assert.prp</propertyfile>
      </tasks>
    </benchmark>
"""

import benchexec.tools.template
import benchexec.result as result


class Tool(benchexec.tools.template.BaseTool2):
    """Tool-info for roast."""

    REQUIRED_PATHS = ["."]

    def executable(self, tool_locator):
        return tool_locator.find_executable("roast")

    def name(self):
        return "roast"

    def project_url(self):
        return "https://github.com/jossmoff/roast"

    def version(self, executable):
        return self._version_from_tool(executable, arg="--version")

    def cmdline(self, executable, options, task, rlimits):
        cmd = [executable]
        cmd.extend(options)

        # BenchExec passes each entry of the task YAML's input_files as a
        # separate path.  roast accepts them as positional arguments.
        cmd.extend(task.input_files_or_identifier)

        return cmd

    def determine_result(self, run):
        """Parse the verdict from roast's stdout.

        roast prints exactly one line to stdout: TRUE, FALSE, or UNKNOWN.
        Everything else goes to stderr and is not relevant for the verdict.
        """
        for line in run.output:
            stripped = line.strip()
            if stripped == "TRUE":
                return result.RESULT_TRUE_PROP
            if stripped == "FALSE":
                return result.RESULT_FALSE_REACH
            if stripped == "UNKNOWN":
                return result.RESULT_UNKNOWN

        # No verdict line found -- treat as error.
        return "ERROR"
