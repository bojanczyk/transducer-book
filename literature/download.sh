#!/bin/bash

# Enhanced Sci-Hub PDF Downloader
# Properly handles URL encoding and special characters in DOIs

if [ $# -eq 0 ]; then
    echo "Usage: $0 <DOI>"
    echo "Example: $0 10.1002/j.1538-7305.1955.tb03788.x"
    echo "Example: $0 10.1007/978-3-662-43951-7_10"
    exit 1
fi

DOI="$1"
# URL encode the DOI for proper handling
ENCODED_DOI=$(echo "$DOI" | sed 's/\//%2F/g; s/_/%5F/g; s/:/%3A/g; s/ /%20/g')
SCI_HUB_URL="https://sci-hub.pl"
OUTPUT_FILE=$(echo "$DOI" | tr '/' '_' | tr '.' '_' | sed 's/_$//').pdf

echo "Processing: $DOI"
echo "Encoded DOI: $ENCODED_DOI"

# Create temp directory
TEMP_DIR=$(mktemp -d)
trap "rm -rf $TEMP_DIR" EXIT

# Try multiple Sci-Hub domains if one fails
SCI_HUB_DOMAINS=("https://sci-hub.pl" "https://sci-hub.se" "https://sci-hub.st" "https://sci-hub.ru")

for BASE_URL in "${SCI_HUB_DOMAINS[@]}"; do
    echo "Trying $BASE_URL..."
    
    # Fetch the page with proper headers
    curl -s -L -c "$TEMP_DIR/cookies.txt" \
        -H "User-Agent: Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36" \
        -H "Accept: text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8" \
        -o "$TEMP_DIR/page.html" \
        "$BASE_URL/$ENCODED_DOI"
    
    # Check if we got a response
    if [ ! -s "$TEMP_DIR/page.html" ]; then
        echo "  ✗ Failed to fetch page"
        continue
    fi

    # Debug: show the page title if available
    PAGE_TITLE=$(grep -o '<title>[^<]*</title>' "$TEMP_DIR/page.html" | sed 's/<title>//;s/<\/title>//')
    echo "  Page title: $PAGE_TITLE"

    # Check if page contains the article (not an error page)
    if echo "$PAGE_TITLE" | grep -qi "error\|not found\|404"; then
        echo "  ✗ Page shows error, trying next domain..."
        continue
    fi

    # Look for the PDF in multiple ways
    PDF_URL=""

    # Method 1: Look for citation_pdf_url meta tag (MOST COMMON for Sci-Hub)
    PDF_URL=$(grep -o 'citation_pdf_url" content="[^"]*"' "$TEMP_DIR/page.html" | head -1 | sed 's/.*content="//;s/"$//')
    if [ -n "$PDF_URL" ]; then
        echo "  Found PDF via citation_pdf_url meta tag"
    fi

    # Method 2: Look for the iframe that contains the PDF
    if [ -z "$PDF_URL" ]; then
        PDF_URL=$(grep -o 'src="//[^"]*\.pdf"' "$TEMP_DIR/page.html" | head -1 | sed 's/^src="//;s/"$//')
        if [ -n "$PDF_URL" ] && [[ $PDF_URL == //* ]]; then
            PDF_URL="https:$PDF_URL"
        fi
    fi

    # Method 3: Look for embed tag
    if [ -z "$PDF_URL" ]; then
        PDF_URL=$(grep -o 'src="[^"]*\.pdf"' "$TEMP_DIR/page.html" | head -1 | sed 's/^src="//;s/"$//')
    fi

    # Method 4: Look for data-pdf attribute
    if [ -z "$PDF_URL" ]; then
        PDF_URL=$(grep -o 'data-pdf="[^"]*"' "$TEMP_DIR/page.html" | head -1 | sed 's/^data-pdf="//;s/"$//')
    fi

    # Method 5: Look for any PDF URL in the page (with flexible pattern)
    if [ -z "$PDF_URL" ]; then
        # Look for PDF links without requiring https:// at the start
        PDF_URL=$(grep -oE 'https?://[^"]*\.pdf|[^"]*\.pdf' "$TEMP_DIR/page.html" | grep -v '\.js' | head -1)
        # Fix relative URLs
        if [ -n "$PDF_URL" ] && [[ $PDF_URL != http* ]]; then
            if [[ $PDF_URL == //* ]]; then
                PDF_URL="https:$PDF_URL"
            elif [[ $PDF_URL == /* ]]; then
                PDF_URL="$BASE_URL$PDF_URL"
            else
                PDF_URL="$BASE_URL/$PDF_URL"
            fi
        fi
    fi

    # Method 6: Look for the direct link in JavaScript
    if [ -z "$PDF_URL" ]; then
        PDF_URL=$(grep -o "window\.location[^']*'[^']*'" "$TEMP_DIR/page.html" | grep -o "'[^']*\.pdf'" | sed "s/'//g" | head -1)
    fi

    # Method 7: Look for the embed PDF in the page source
    if [ -z "$PDF_URL" ]; then
        PDF_URL=$(grep -o 'data="[^"]*\.pdf"' "$TEMP_DIR/page.html" | head -1 | sed 's/^data="//;s/"$//')
    fi

    # Method 8: Look for any PDF link in the page content
    if [ -z "$PDF_URL" ]; then
        PDF_URL=$(grep -o '/storage/[^"]*\.pdf' "$TEMP_DIR/page.html" | head -1)
        if [ -n "$PDF_URL" ]; then
            PDF_URL="$BASE_URL$PDF_URL"
        fi
    fi

    # Method 9: Look for PDF in the iframe's src attribute specifically
    if [ -z "$PDF_URL" ]; then
        PDF_URL=$(grep -o 'iframe[^>]*src="[^"]*"' "$TEMP_DIR/page.html" | grep -o 'src="[^"]*"' | head -1 | sed 's/^src="//;s/"$//')
        if [ -n "$PDF_URL" ] && [[ $PDF_URL == //* ]]; then
            PDF_URL="https:$PDF_URL"
        elif [ -n "$PDF_URL" ] && [[ $PDF_URL == /* ]]; then
            PDF_URL="$BASE_URL$PDF_URL"
        fi
    fi

    # Check if we found the PDF
    if [ -z "$PDF_URL" ]; then
        echo "  ✗ Could not find PDF URL on $BASE_URL."
        echo "  Trying next domain..."
        continue
    fi

    # Fix the URL - handle relative paths
    if [[ $PDF_URL == //* ]]; then
        PDF_URL="https:$PDF_URL"
    elif [[ $PDF_URL == /* ]]; then
        # If it starts with /, it's relative to the domain
        PDF_URL="$BASE_URL$PDF_URL"
    elif [[ $PDF_URL != http* ]]; then
        # If it doesn't have a protocol, assume it's relative
        PDF_URL="$BASE_URL/$PDF_URL"
    fi

    echo "  Found PDF URL: $PDF_URL"
    echo "  Downloading: $OUTPUT_FILE"

    # Download the PDF with proper headers
    curl -L -b "$TEMP_DIR/cookies.txt" \
        -H "User-Agent: Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36" \
        -H "Referer: $BASE_URL" \
        -H "Accept: application/pdf,text/html,application/xhtml+xml" \
        -o "$OUTPUT_FILE" \
        "$PDF_URL"

    # Verify download
    if [ -f "$OUTPUT_FILE" ] && [ -s "$OUTPUT_FILE" ]; then
        # Check if it's a PDF
        if head -c 4 "$OUTPUT_FILE" 2>/dev/null | grep -q "%PDF"; then
            SIZE=$(du -h "$OUTPUT_FILE" | cut -f1)
            echo "✓ Success! Downloaded as: $OUTPUT_FILE (Size: $SIZE)"
            exit 0
        else
            echo "  ⚠ Downloaded but may not be a valid PDF."
            echo "  File type: $(file "$OUTPUT_FILE" 2>/dev/null || echo 'unknown')"
            # Continue trying other domains if download wasn't valid
            rm -f "$OUTPUT_FILE"
        fi
    else
        echo "  ✗ Download failed on $BASE_URL"
        rm -f "$OUTPUT_FILE"
        continue
    fi
done

# If we got here, all domains failed
echo ""
echo "✗ Failed to download PDF from all Sci-Hub domains."
echo "Try opening in browser: https://sci-hub.pl/$ENCODED_DOI"
echo ""
echo "Debug: The page content suggests the article exists but the PDF URL couldn't be extracted."
echo "Page content sample (first 1000 chars):"
head -c 1000 "$TEMP_DIR/page.html"
exit 1