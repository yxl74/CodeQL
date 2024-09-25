import java
import semmle.code.java.frameworks.android.Android
import semmle.code.java.frameworks.android.Intent

from AndroidComponent component, string componentType
where
  (component instanceof Activity and componentType = "Activity") or
  (component instanceof Service and componentType = "Service") or
  (component instanceof ContentProvider and componentType = "Content Provider") or
  (component instanceof BroadcastReceiver and componentType = "Broadcast Receiver")
select componentType, component.getQualifiedName()
