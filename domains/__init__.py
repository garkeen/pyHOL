"""Domain extensions for holpy.

Each subpackage registers domain-specific conv, macro, and method classes
via the decorators in kernel.theory / server.methods.core / logic.auto.

A domain is loaded by basic.py when the corresponding .pyhol file declares
`domains <name>` in its header. The import triggers @register_* decorators,
making the domain's macro/method/conv available to the proof system.
"""
