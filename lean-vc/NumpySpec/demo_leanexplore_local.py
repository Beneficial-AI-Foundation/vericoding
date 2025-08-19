#!/usr/bin/env python3
"""Demo: Search for 'qsort' using LeanExplore local backend (NO API KEY NEEDED)"""

from lean_explore.local.service import Service as LocalService
from rich.console import Console
from rich.panel import Panel

console = Console()

def demo_local_search():
    """Demonstrate local search without API keys"""
    console.print("\n[bold cyan]═══ LeanExplore Local Search Demo ═══[/bold cyan]\n")
    console.print("[yellow]Running entirely locally - NO API KEY REQUIRED![/yellow]\n")
    
    # Initialize local service
    service = LocalService()
    console.print("✅ Local service initialized")
    console.print(f"📁 Using data from: ~/.lean_explore/data/toolchains/\n")
    
    # Search for 'qsort'
    query = "qsort"
    console.print(f"🔍 Searching for: [bold]{query}[/bold]")
    
    try:
        response = service.search(query, limit=5)
        results = response.results if hasattr(response, 'results') else []
        
        if not results:
            console.print(f"\nNo results for '{query}'. Trying 'sort' instead...")
            query = "sort"
            response = service.search(query, limit=5)
        results = response.results if hasattr(response, 'results') else []
        
        if results:
            console.print(f"\n[green]Found {len(results)} results:[/green]\n")
            
            for i, result in enumerate(results, 1):
                # Get primary declaration info
                if hasattr(result, 'primary_declaration') and result.primary_declaration:
                    name = result.primary_declaration.lean_name
                    kind = result.primary_declaration.kind if hasattr(result.primary_declaration, 'kind') else 'Unknown'
                else:
                    name = 'Unknown'
                    kind = 'Unknown'
                
                # Get source file
                source_file = result.source_file if hasattr(result, 'source_file') else 'Unknown'
                
                # Create result panel
                content = f"[bold]Name:[/bold] {name}\n"
                content += f"[bold]Type:[/bold] {kind}\n"
                content += f"[bold]File:[/bold] {source_file}"
                
                if hasattr(result, 'docstring') and result.docstring:
                    doc = result.docstring
                    if len(doc) > 150:
                        doc = doc[:150] + "..."
                    content += f"\n\n[dim]{doc}[/dim]"
                
                console.print(Panel(
                    content,
                    title=f"Result {i}",
                    border_style="blue"
                ))
                console.print()
        else:
            console.print(f"\n[red]No results found for '{query}'[/red]")
            
    except Exception as e:
        console.print(f"\n[red]Error: {e}[/red]")
        console.print("\n[yellow]Tip: Make sure local data is downloaded:[/yellow]")
        console.print("  uv run leanexplore data fetch")
    
    console.print("\n[bold green]✨ Demo complete - all searches performed locally![/bold green]")

if __name__ == "__main__":
    demo_local_search()