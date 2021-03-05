package de.ovgu.spldev.keypr.aoeu;

import java.awt.*;
import java.awt.datatransfer.StringSelection;

public class Util {
    public interface IDot {
        String toDotString();

        default IDot copyDotString() {
            Toolkit.getDefaultToolkit().getSystemClipboard().setContents(new StringSelection(toDotString()), null);
            return this;
        }
    }
}
