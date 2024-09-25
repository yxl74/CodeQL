import java
import semmle.code.java.frameworks.android.Android

predicate isAndroidComponent(RefType t, string componentType) {
  t.getASupertype*().hasQualifiedName("android.app", "Activity") and componentType = "Activity"
  or
  t.getASupertype*().hasQualifiedName("android.app", "Service") and componentType = "Service"
  or
  t.getASupertype*().hasQualifiedName("android.content", "ContentProvider") and componentType = "Content Provider"
  or
  t.getASupertype*().hasQualifiedName("android.content", "BroadcastReceiver") and componentType = "Broadcast Receiver"
}

from RefType component, string componentType
where isAndroidComponent(component, componentType)
select componentType, component.getQualifiedName()
